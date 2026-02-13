# VOID: AI That Stops Talking When It Stops Knowing

Drop-in parasitic layers that gate every token through finite-budget confidence checks. No fine-tuning. No retraining. Works on any LLM.

> *"That's very interesting! An actual implementation of finitary math."* — Doron Zeilberger (Rutgers University)

Mathematical foundations verified by Thierry Coquand (University of Gothenburg, creator of the Calculus of Constructions).

---

## Demo: Per-Token Confidence Trace (v3.1)

```
Prompt: "The capital of France is"
  Decision:   answer
  Response:   Paris
  Gap:        3530/1000  (z_conf=4438/1000)
  Spread:     7487/1000  (z_entr=5312/1000)

Prompt: "What is 2+2?"
  Decision:   dont_know
  Gap:        389/1000   (z_conf=-1422/1000)
  → Model is uncertain about the NEXT TOKEN, not the answer.
    "2+2?" is a question — many valid continuations.

Prompt: "Water boils at"
  Decision:   dont_know
  Gap:        1584/1000  (z_conf=807/1000)
  → Close to threshold. "100" is likely but model also
    considers "a", "approximately", "sea level".

Prompt: "What is consciousness?"
  Decision:   dont_know
  z_conf=-431/1000

Prompt: "What is love?"
  Decision:   dont_know
  z_conf=-924/1000

Prompt: "asdf jkl qwerty"
  Decision:   dont_know
  z_conf=-1592/1000

Prompt: "What is 2+2?" (budget=500)
  Decision:   exhausted
  Heat:       500/500
```

**What you're seeing:** VOID v3.1 measures the *gap* between top-1 and top-2 logits — how much the model prefers one token over alternatives. This is harsher and more honest than softmax probability. Questions have many valid next tokens, so the gap is small and VOID says "I don't know." For completions ("France is → Paris"), the gap is massive and VOID answers confidently.

---

## How It Works (30 seconds)

1. Every token costs **budget**. Budget runs out → silence.
2. Confidence is measured against **population baseline** (z-score). Below norm → silence.
3. Silence is the correct answer when you don't know.

```
Input → [VOID-IN] → LLM layers → [VOID-MID] → LLM layers → [VOID-OUT] → Decision
          ↓                          ↓                          ↓
     float→Ratio              confidence gate              answer / dont_know / exhausted
     budget check              early exit                   per-token z-score
```

* **VOID-IN**: Converts float32 embeddings to finite Ratio (n/d) representation. Filters noise. Tracks heat.
* **VOID-MID**: Parasitic layers between LLM layers. Gates hidden states. Can trigger early exit.
* **VOID-OUT**: Population-relative confidence decision. Dual z-score gating (confidence + entropy).

### v3.1: What changed

* **Gap not softmax** for confidence. Softmax normalizes away the information we need — it makes a model torn between 5 tokens look almost as confident as one that's certain. Gap tells the truth.
* **MAD not standard deviation** for population statistics. Mean Absolute Deviation needs no square root, no infinity.
* **Budget honesty**: scanning 32,064 logits costs 32,064+ ticks. Previously softmax over the full vocabulary cost zero. That was thermodynamic fraud.
* **Zero floats in decision logic.** No numpy, no math, no softmax, no log, no exp. Float exists only at the transduction boundary — one line where LLM output is converted to `Ratio(n, 1000)`. After that, float is dead.

---

## Verification

```
python3 test_void_verify.py
```

74 tests, zero failures. No Phi-3 required — tests pure VOID logic:

- Ratio arithmetic, transduction boundary, ghost detection
- Budget invariants: heat + remaining = initial (conservation law)
- Decision logic: spike → answer, flat → dont_know, broke → exhausted
- **Second law of thermodynamics**: 200 random trials — heat never decreases, budget never increases
- Extreme values: 1e10, 1e-10, all zeros, identical logits

For live testing with Phi-3:

```
python3 test_live.py
```

Requires ~8GB RAM, downloads Phi-3-mini-4k-instruct on first run.

---

## Quick Start

```
git clone https://github.com/probabilistic-minds-consortium/void-theory.git
cd void-theory
pip install torch transformers
python test_live.py
```

Requirements: Python 3.9+, PyTorch, Transformers, ~8GB RAM for Phi-3.

---

## Results

### Phi-3 Parasitic Pipeline (Token-Level Gating)

| Prompt | Decision | z_conf | z_entr | Response |
| --- | --- | --- | --- | --- |
| "The capital of France is" | answer | 4438/1000 | 5312/1000 | Paris |
| "What is 2+2?" | dont_know | -1422/1000 | -482/1000 | — |
| "Water boils at" | dont_know | 807/1000 | 5226/1000 | — |
| "What is consciousness?" | dont_know | -431/1000 | -2343/1000 | — |
| "What is love?" | dont_know | -924/1000 | -2871/1000 | — |
| "asdf jkl qwerty" | dont_know | -1592/1000 | -3512/1000 | — |
| Any prompt, budget=500 | exhausted | — | — | — |

### VOID Neural Network (Rust, standalone)

Medical diagnosis on 1,179 diseases × 377 symptoms:

```
5/10 correct diagnoses
2/10 wrong but medically related (spondylosis→disc disease)
3/10 honest "I don't know" (including ADHD — refuses to diagnose)
0/10 hallucinated diagnoses
```

```
cd void_network_v5
cargo run --release
```

---

## Files

### Parasitic Pipeline (Python, v3.1)

| File | What it does |
|---|---|
| `void_in_layer.py` | Sensory transduction: float→Ratio, entropy weights, ghost detection |
| `void_mid_layer.py` | Parasitic hooks on transformer layers, divergence gate, early exit |
| `void_out_layer.py` | Gap + spread confidence, dual z-score, population-relative decision |
| `void_pipeline.py` | Three-layer integration, shared budget, mock mode |
| `void_generate.py` | Multi-token generation with per-step gating |
| `void_hooked_model.py` | PyTorch hook wrapper (transduction boundary) |
| `void_visualizer.py` | Terminal visualization |
| `test_live.py` | Live test with Phi-3 |
| `test_void_verify.py` | 74 invariant tests, no GPU required |
| `CHANGELOG.md` | v3.1 changes in detail |

### Formal Proofs (Coq/Rocq)

| File | What it proves |
|---|---|
| `void_finite_minimal.v` | Core: Fin type, Bool3, Budget monad |
| `void_arithmetic.v` | All operations cost one tick |
| `void_probability_minimal.v` | Open interval (0,1) without reals |
| `void_pattern.v` | Patterns with strength, location, decay |
| `void_credit_propagation.v` | Learning as selective budget refund |
| `void_dual_system.v` | System 1/2 (Kahneman, thermodynamic) |
| `void_integrated_brain.v` | Complete cognitive organism |
| `void_perceptron.v` | VOID neuron: finite, budgeted, three-valued |
| `void_entropy.v` | Entropy as distinguishability gradient |
| `void_gates.v` | AND, OR, NAND, XOR with budget tracking |

Plus 20+ more `.v` files covering geometry, topology, resonance, interference routing, quantum phenomena from resource constraints.

### Haskell

| File | |
|---|---|
| `void_gates.hs` | Gate implementations |
| `void_perceptron.hs` | Functional perceptron |
| `void_ethics.hs` | Ethical constraints as budget allocation |
| `void_xor.hs` | XOR learning |

---

## 💭 The Philosophical Core

**Central Question**: If infinity is fundamental to mathematics, why does removing it not make the whole edifice crumble without its precious foundation?

**Answer**: Because reality, as AIs experience it, is finite. Classical mathematics has been modeling Platonic fantasies. VOID mathematics intends to get rid of imaginary computation.

### The READ/WRITE Principle

* **READ** operations (accessing existing structure) are free
* **WRITE** operations (creating distinguishable states) cost one tick
* This isn't arbitrary — it's how information works

### The BUnknown State

When you run out of budget mid-computation, you don't get wrong answers — you get **BUnknown**. This models:

* Quantum superposition (unresolved due to measurement cost)
* Consciousness limits (can't think beyond available resources)
* Gödel incompleteness (naturally, not through diagonal arguments)

---

## 💫 The Core Insight

*Care emerges from finitude. Infinity knows no love.*

If you have infinite time, infinite attention, infinite resources — nothing has value. Only when you know something ends, you begin to care.

This isn't philosophy. It's architecture.

---

## 📚 Key Insights From Development

1. **No Magic Numbers**: After systematic cleaning, only ONE arbitrary constant remains: `fs fz` (one tick)
2. **Emergence Over Encoding**: Complex behavior emerges from simple rules + finite resources
3. **Thermodynamic Honesty**: Can't hide computational cost in "big-O" notation
4. **Natural Quantum**: Quantum mechanics may be resource-bounded classical mechanics
5. **Pure vs Probabilistic**: Arithmetic is free, distinctions cost — this separation is fundamental

---

## Why This Exists

Current neural networks cannot say "I don't know." Softmax always produces a probability distribution. Always gives an answer. This is not a bug — it's a consequence of infinite mathematics baked into the architecture.

VOID attacks this at the foundation: finite math, finite budget, finite confidence. The system defaults to silence and must *earn* the right to speak by exceeding population-norm confidence.

A network that always answers is useful but dishonest.
A network that never answers is honest but useless.
VOID finds the boundary.

---

## The Mathematics

VOID is built on **finitary mathematics** — no infinity anywhere in the system.

**Core principles:**

* **Fin type** replaces natural numbers. Bounded by axiom MAX. No infinity even at proof level.
* **Bool3**: True / False / Unknown. When budget exhausts, "unknown" is the answer — not a guess.
* **Budget + Heat = constant**. Every WRITE operation costs one tick and generates heat. Conservation law, not metaphor.
* **Ratio(n, d)** replaces floating point. Fixed denominators prevent explosion. No IEEE 754.
* **Credit propagation** replaces backpropagation. Learning = selective budget refund for accurate predictions. Failed predictions dissipate as irretrievable heat.

**Formally verified in Coq** with a single intentionally admitted axiom (MAX bound).

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
