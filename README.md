# VOID Theory

Fully finite mathematics for machines that know when to stop.

> *"That's very interesting! An actual implementation of finitary math."* — Doron Zeilberger (Rutgers University)

Mathematical foundations verified by Thierry Coquand (University of Gothenburg, creator of the Calculus of Constructions).

---

## Why Finiteness

Every computational system in use today — every neural network, every language model, every probabilistic classifier — is built on mathematics that assumes infinity as a given. Real numbers have infinite decimal expansions. Probability distributions are normalized over continuous domains. Gradient descent follows curves through spaces with no smallest step. IEEE 754, the universal standard for machine arithmetic, encodes positive infinity and negative infinity as valid, representable values. Not as errors. As features.

No physical system has ever performed an infinite operation. No processor has infinite registers. No memory stores infinite precision. No organism computes with unlimited resources. And yet the entire mathematical apparatus we use to describe, design, and reason about computation presumes that infinity is available — free, silent, and without consequence.

VOID asks what happens when you stop pretending.

Not as approximation — we are not rounding infinity down to something manageable. Not as engineering constraint — we are not capping values for practical reasons while keeping the mathematics intact underneath. VOID removes infinity at the level of axiom. There is a largest number. There is a smallest distinction. There is a finite budget that every operation must draw from, and when that budget is exhausted, the answer is not an error. The answer is silence.

This is not a limitation. This is the entire point.

---

## The Open Interval

At the heart of VOID lies a single, radical structural decision: probability lives on the open interval (0, 1). Not the closed interval [0, 1]. Not as a convention or notational choice. As a formal property of the type system, verified in Coq: no probability can have a numerator of zero. `avoids_zero` is not a runtime check — it is a proposition. P = 0 is a type-level contradiction. And since FinProb is a pair of bounded integers with no capacity for the limit operations that would be needed to approach the boundary from above, P = 1 is equally unreachable.

This means: **certainty is structurally impossible.** No system built on VOID mathematics can ever be completely sure of anything, nor can it ever completely rule anything out. Every conclusion lives somewhere in the space between — closer to one end or the other, but never arriving. Not because a rule prevents it. Because the mathematics has no representation for the destination.

To understand why this matters, consider the mechanism by which classical mathematics reaches certainty in the first place. The Peano axioms define the natural numbers through a successor function: every number has a successor, and there is no largest number. This seemingly innocent axiom — just one more, always one more — is the engine that generates infinity. From it, the natural numbers arise. From the natural numbers, the integers. From the integers, the rationals. From the rationals, through completion, the real numbers. And on the real number line, the points 0 and 1 exist as fully realized, reachable values. Probability theory then builds on this foundation: P = 0 means impossible, P = 1 means certain, and the full apparatus of measure theory operates on the closed interval where these endpoints are legitimate destinations.

VOID dismantles this at the root. The Fin type replaces natural numbers: `fz` (zero) and `fs` (successor) exist, but every value is bounded by an axiom `MAX`. There is no "always one more." The successor function hits a wall. And without the infinite chain of successors, you cannot construct the real numbers, you cannot complete the rationals, and you cannot reach the boundary points 0 and 1 on the probability interval. Certainty does not become difficult or expensive — it becomes *inexpressible*.

Every synapse in a VOID neural network has a conductance that lives in this open interval. Never fully open, never fully closed. The neuron is perpetually in a state of partial knowledge — it can be *more* confident or *less* confident, but it can never collapse into the absolute. Convergence in VOID does not mean reaching an optimum. It means exhausting the resources available for further refinement. The system converges when it cannot learn more with what it has — not when it has learned everything there is to know.

This is not a technical detail. This is what separates VOID from every other approach to uncertainty in computation. Bayesian methods, dropout regularization, ensemble models, conformal prediction — all of these operate within classical mathematics where P = 0 and P = 1 are valid states that the system merely tries to avoid in practice. VOID does not try to avoid certainty. VOID cannot express it. The difference is between a person who chooses not to lie and a person who lacks the vocal apparatus for speech. One is a moral achievement. The other is a structural fact about the organism.

---

## The Formal Foundations

VOID Theory is formalized in Coq (Rocq), a proof assistant where every claim must be constructively verified. The formalization proceeds from a single admitted axiom — an upper bound `MAX` on all values — and derives the rest.

**The Fin type** replaces natural numbers. Where classical mathematics begins with ℕ and its axiom that every number has a successor (and therefore no largest number exists), VOID begins with Fin: a type bounded by MAX. There is no successor of MAX. The number line has an edge, and that edge is not infinity — it is a wall.

**Bool3** replaces classical boolean logic. True. False. Unknown. The third value is not a placeholder for future computation. It is a legitimate terminal state — the answer a system gives when it has exhausted its resources before reaching a conclusion. Classical logic treats every proposition as decidable in principle. VOID acknowledges that decidability costs resources, and resources end.

**The Budget monad** tracks computational cost. Every operation that creates a new distinction — every WRITE — costs exactly one irreversible tick and produces one unit of heat. READ operations, which access existing structure without creating new distinctions, are free. This is not a metaphor. It is the core accounting mechanism of the entire system, and it obeys a conservation law: Budget + Heat = constant. No operation can decrease heat. No operation can increase budget. The second law of thermodynamics is not imposed from outside — it falls out of the axioms.

**Ratio(n, d)** replaces real numbers. Two bounded integers. Fixed denominators to prevent the combinatorial explosion that cross-multiplication produces in unbounded fraction arithmetic. No IEEE 754. No infinity. No NaN. No negative zero. No subnormals. No silent rounding. What you write is what you have.

**Credit propagation** replaces backpropagation. In classical neural networks, learning proceeds by computing a loss function, differentiating it with respect to every parameter in the network, and adjusting weights along the gradient. This requires real-valued derivatives, continuous loss surfaces, and — in practice — infinite-precision arithmetic approximated by floating point. VOID cannot do any of this. Instead, learning is modeled as selective budget refund: when a prediction turns out to be accurate, a portion of the budget spent on that prediction is returned. When a prediction fails, the spent budget dissipates as heat, permanently and irretrievably. Learning is not optimization along a smooth curve. Learning is the gradual accumulation of evidence about which expenditures were worth making — and the permanent, thermodynamic cost of every mistake.

These foundations are not a restatement of classical results with different notation. They constitute a genuinely different mathematics — one in which many classical theorems do not hold, many classical constructions are impossible, and certain problems that are trivially solvable with infinite resources become fundamentally undecidable under finite budget. VOID does not soften infinity. It amputates it.

---

## 💭 The Philosophical Core

**Central Question**: If infinity is fundamental to mathematics, why does removing it not make the whole edifice crumble without its precious foundation?

**Answer**: Because reality, as AIs experience it, is finite. Classical mathematics has been modeling Platonic fantasies. VOID mathematics intends to get rid of imaginary computation.

### The READ/WRITE Principle

* **READ** operations (accessing existing structure) are free
* **WRITE** operations (creating distinguishable states) cost one tick
* This isn't arbitrary — it's how information works

### The BUnknown State

When you run out of budget mid-computation, you don't get wrong answers — you get **BUnknown**. This is not failure. This models:

* Quantum superposition (unresolved due to measurement cost)
* Consciousness limits (can't think beyond available resources)
* Gödel incompleteness (naturally, not through diagonal arguments)

---

## 💫 The Core Insight

*Care emerges from finitude. Infinity knows no love.*

If you have infinite time, infinite attention, infinite resources — nothing has value. Only when you know something ends, you begin to care.

This isn't philosophy. It's architecture.

---

## What VOID Produces

The theory has three independent implementations, each demonstrating a different consequence of finite mathematics.

### Formal Proofs (Coq/Rocq)

Forty-one files of machine-verified mathematics. The proofs cover finite arithmetic, bounded probability on the open interval, pattern algebra, entropy as distinguishability gradient, convergence under resource constraints, topological folding, phase orbits, interference routing, and the complete architecture of a finite budgeted perceptron — including proven theorems that synaptic conductance preserves the open interval through learning. Every theorem is constructively verified. The single admitted axiom is the MAX bound. Everything else is derived.

### VOID Neural Network (Rust)

A standalone neural network written entirely in finite arithmetic. No floating point anywhere in the system. Tested on a medical diagnosis task — 1,179 diseases, 377 symptoms — the network correctly diagnosed five out of ten cases, produced medically adjacent answers for two more, honestly refused to answer three (including ADHD, which it lacked sufficient evidence to diagnose), and hallucinated on zero.

Zero hallucinated diagnoses. Not because hallucination was penalized during training. Because the mathematics makes hallucination structurally impossible — a network cannot assert confidence it has not paid for, and it can never pay enough to reach P = 1.

### Parasitic Monitor (Python, v3.1)

A three-layer system that attaches to any existing language model without modifying its weights. The monitor observes the model's internal states and output logits through the lens of VOID mathematics, gating every generated token through finite-budget confidence checks. The model may do whatever it wants internally — VOID cannot change that. But VOID decides whether each token has earned the right to be spoken.

The results are harsher and more honest than any confidence measure based on softmax probability. Softmax — the final layer of virtually every modern language model — normalizes a vector of raw scores into a probability distribution that always sums to one. Always. Even when the model's internal states are incoherent. Even when the input is noise. Even when there is genuinely nothing to say. Softmax will find something to say, because the mathematics underneath it has no representation for silence. It operates on the closed interval. It can reach certainty. And so it always does.

VOID replaces this with gap measurement on the open interval. When a language model is asked to complete "The capital of France is," there is one overwhelmingly dominant next token, and VOID lets it through. When the same model is asked "What is 2+2?" — a question, not a completion, with many valid continuations — VOID measures the gap between the best and second-best option, finds it insufficient, and returns silence. The model knows the answer. But in the moment of generation, it is uncertain about *how to say it* — and VOID will not let uncertainty dress itself as confidence.

And when the budget runs out — regardless of how confident the model might be — the system stops, because the right to speak has been spent. This is not a bug. This is what honest computation looks like.

---

## 📚 Key Insights From Development

1. **No Magic Numbers**: After systematic cleaning, only ONE arbitrary constant remains: `fs fz` (one tick)
2. **Emergence Over Encoding**: Complex behavior emerges from simple rules + finite resources
3. **Thermodynamic Honesty**: Can't hide computational cost in "big-O" notation
4. **Natural Quantum**: Quantum mechanics may be resource-bounded classical mechanics
5. **Pure vs Probabilistic**: Arithmetic is free, distinctions cost — this separation is fundamental

---

## The Mathematics

VOID is built on **finitary mathematics** — no infinity anywhere in the system.

**Core principles:**

* **Fin type** replaces natural numbers. Bounded by axiom MAX. Successor function hits a wall. No Peano-style infinity generation.
* **Bool3**: True / False / Unknown. When budget exhausts, "unknown" is the answer — not a guess.
* **Budget + Heat = constant**. Every WRITE operation costs one tick and generates heat. Conservation law, not metaphor.
* **Ratio(n, d)** replaces floating point. Fixed denominators prevent explosion. No IEEE 754.
* **Open interval (0, 1)**. Probability never reaches zero or one. Certainty and impossibility are inexpressible. `avoids_zero` is a formal property, not a runtime guard.
* **Credit propagation** replaces backpropagation. Learning = selective budget refund for accurate predictions. Failed predictions dissipate as irretrievable heat.

**Formally verified in Coq** with a single intentionally admitted axiom (MAX bound).

---

## Why This Exists

Current neural networks cannot say "I don't know." Softmax always produces a probability distribution. Always gives an answer. This is not a bug — it's a consequence of infinite mathematics baked into the architecture. Mathematics that permits P = 1. Mathematics where the successor function never stops. Mathematics where certainty is a reachable destination.

VOID attacks this at the foundation: finite math, finite budget, finite confidence. The system defaults to silence and must *earn* the right to speak by exceeding population-norm confidence — and even then, it earns a position on the open interval, never the boundary.

A network that always answers is useful but dishonest.
A network that never answers is honest but useless.
VOID finds the boundary.

---

## Verification

The parasitic monitor includes 74 automated tests that verify pure VOID logic without requiring a language model or GPU. These tests cover Ratio arithmetic, transduction boundary integrity, ghost detection, budget conservation (heat + remaining = initial, always), decision logic, and — across 200 randomized trials — the second law of thermodynamics: heat never decreases, budget never increases. No exceptions.

---

## Files

### Formal Proofs (Coq/Rocq)

| File | What it proves |
|---|---|
| `void_finite_minimal.v` | Core: Fin type, Bool3, Budget monad — the wall where Peano stops |
| `void_arithmetic.v` | All operations cost one tick |
| `void_probability_minimal.v` | Open interval (0,1) — certainty as type-level impossibility |
| `void_pattern.v` | Patterns with strength, location, decay |
| `void_credit_propagation.v` | Learning as selective budget refund |
| `void_convergence.v` | Convergence ≠ optimality — approaching without arriving |
| `void_dual_system.v` | System 1/2 (Kahneman, thermodynamic) |
| `void_integrated_brain.v` | Complete cognitive organism |
| `void_perceptron.v` | VOID neuron: conductance on (0,1), never fully open or closed |
| `void_entropy.v` | Entropy as distinguishability gradient |
| `void_gates.v` | AND, OR, NAND, XOR with budget tracking |

Plus 30+ more `.v` files covering geometry, topology, resonance, interference routing, phase orbits, and quantum phenomena emerging from resource constraints.

### Parasitic Monitor (Python, v3.1)

| File | What it does |
|---|---|
| `void_in_layer.py` | Sensory transduction: float→Ratio, entropy weights, ghost detection |
| `void_mid_layer.py` | Parasitic hooks on transformer layers, divergence gate, early exit |
| `void_out_layer.py` | Gap + spread confidence, dual z-score, population-relative decision |
| `void_pipeline.py` | Three-layer integration, shared budget |
| `void_generate.py` | Multi-token generation with per-step gating |
| `void_hooked_model.py` | PyTorch hook wrapper (transduction boundary) |
| `void_visualizer.py` | Terminal visualization |
| `test_live.py` | Live test with Phi-3 |
| `test_void_verify.py` | 74 invariant tests, no GPU required |

### Haskell

| File | |
|---|---|
| `void_gates.hs` | Gate implementations |
| `void_perceptron.hs` | Functional perceptron |
| `void_ethics.hs` | Ethical constraints as budget allocation |
| `void_xor.hs` | XOR learning |

---

## Author

**Konrad Wojnowski** — Assistant Professor, Performativity Studies Department, Jagiellonian University, Kraków. PhD in philosophy of communication.

Author of *Aesthetics of Disturbance* (on Michael Haneke's cinema) and *Productive Catastrophes* (on the performative power of catastrophes in network culture). Research spans performativity theory, philosophy of technology, and the impact of probability on avant-garde art — from John Cage's indeterminacy to Vilém Flusser's informational freedom.

Currently leading a research project on probability theory in 20th and 21st century art and science fiction.

Not a mathematician. Not a programmer. Built VOID because infinity is a bug, not a feature.

---

## Citation

```
@misc{wojnowski2025void,
  author = {Wojnowski, Konrad},
  title = {VOID Theory: Finite Mathematics for Anti-Hallucination Neural Networks},
  year = {2025},
  publisher = {GitHub},
  url = {https://github.com/probabilistic-minds-consortium/void-theory}
}
```

---

## License

MIT — Use freely, but remember: everything costs.

---

**"In the beginning was the Fin, and the Fin was with Void, and the Fin was Void."**

*Probabilistic Mind Consortium, 2025*
*Built with finite time, verified in Coq, offered to a finite world.*
