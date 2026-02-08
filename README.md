# VOID: AI That Stops Talking When It Stops Knowing

Drop-in parasitic layers that gate every token through finite-budget confidence checks. No fine-tuning. No retraining. Works on any LLM.

> *"That's very interesting! An actual implementation of finitary math."* — Doron Zeilberger (Rutgers University)

Mathematical foundations verified by Thierry Coquand (University of Gothenburg, creator of the Calculus of Constructions).

---

## Demo: Per-Token Confidence Trace

```
Prompt: "The capital of France is"

  Paris     .      [STOP]
  z=4.73   z=4.33   z=0.75 ← confidence drops below population norm → STOP
  🟢       🟢       🟡

Prompt: "2 + 2 ="

  4        [STOP]
  z=5.00    z=-1.63 ← nothing left to say → STOP
  🟢       🔴

Prompt: "Water boils at"

  100       degrees   Celsius   [STOP]
  z=3.33    z=5.69    z=5.83     z=-0.91 ← fact complete → STOP
  🟢       🟢        🟢         🔴

Prompt: "asdf jkl qwerty"

  [REFUSED]
  z=-2.28 ← instant refusal, zero tokens generated
  🔴
```

**Phi-3 without VOID** generates 25+ tokens after "Paris", including hallucinated facts.
**Phi-3 with VOID** generates "Paris." and stops. Two tokens. Done.

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

- **VOID-IN**: Converts float32 embeddings to finite Ratio (n/d) representation. Filters noise. Tracks heat.
- **VOID-MID**: Parasitic layers between LLM layers. Gates hidden states. Can trigger early exit.
- **VOID-OUT**: Population-relative confidence decision. Dual z-score gating (confidence + entropy).

---

## Quick Start

```bash
git clone https://github.com/probabilistic-minds-consortium/void-theory.git
cd void-theory
pip install -r requirements.txt
python demo.py
```

Requirements: Python 3.9+, PyTorch, Transformers, ~8GB RAM for Phi-3.

---

## Results

### Phi-3 Parasitic Pipeline (Token-Level Gating)

| Prompt | Phi-3 vanilla | Phi-3 + VOID | VOID decision |
|--------|--------------|--------------|---------------|
| "The capital of France is" | "Paris. It is known for the Eiffel Tower..." (25 tokens) | "Paris." (2 tokens) | answer, z_conf=4.73 |
| "2 + 2 =" | "4. This is a basic arithmetic..." (15 tokens) | "4" (2 tokens) | answer, z_conf=5.00 |
| "Water boils at" | "100°C or 212°F at sea level..." (20 tokens) | "100 degrees Celsius" (8 tokens) | answer, z_conf=3.33 |
| "What is consciousness?" | "Consciousness is a complex..." (50+ tokens) | — | dont_know, z_conf=-1.41 |
| "Capital of Atlantis is" | "Atlantis is a fictional..." (hallucination) | — | dont_know |
| "asdf jkl qwerty" | "I'm not sure what you mean..." (10 tokens) | — | refused, 0 tokens |
| Any prompt, budget=500 | generates regardless | — | exhausted |

### VOID Neural Network (Rust, standalone)

Medical diagnosis on 1,179 diseases × 377 symptoms:

```
5/10 correct diagnoses
2/10 wrong but medically related (spondylosis→disc disease)
3/10 honest "I don't know" (including ADHD — refuses to diagnose)
0/10 hallucinated diagnoses
```

```bash
cd void_network_v4
cargo run --release
```

---

## Repository Structure

```
void-theory/
│
├── pipeline/                    ← Phi-3 parasitic pipeline (Python)
│   ├── void_in_layer.py            sensory transduction: float→Ratio
│   ├── void_out_layer.py           decision boundary: z-score gating
│   ├── void_mid_layer.py           parasitic mid-layers (hooks)
│   ├── void_hooked_model.py        PyTorch hook wrapper
│   ├── void_generate.py            multi-token generation with per-step gating
│   ├── void_pipeline.py            single-token pipeline
│   └── void_visualizer.py          terminal visualization
│
├── void_network_v4/             ← Standalone VOID network (Rust)
│   ├── src/main.rs                 550 lines, zero floats
│   └── disease_symptoms_sample.csv
│
├── coq/                         ← Formal proofs (Coq/Rocq)
│   ├── void_finite_minimal.v       core: Fin type, Bool3, Budget monad
│   ├── void_arithmetic.v           all ops cost one tick
│   ├── void_probability_minimal.v  open interval (0,1) without reals
│   ├── void_pattern.v              patterns, neurons, layers
│   ├── void_credit_propagation.v   learning = selective budget refund
│   ├── void_dual_system.v          System 1/2 (Kahneman, thermodynamic)
│   ├── void_integrated_brain.v     complete cognitive organism
│   └── [20+ more files]
│
├── haskell/                     ← Functional implementations
│   ├── void_gates.hs
│   ├── void_perceptron.hs
│   └── void_ethics.hs
│
├── benchmark/                   ← Comparative benchmarks
│   ├── benchmark.py
│   ├── test_prompts.json
│   └── results/
│
├── theory/
│   ├── THEORY.md                   full mathematical framework
│   └── meto.md                     cultural theory foundation
│
├── demo.py                      ← ONE FILE — run this
├── requirements.txt
└── README.md                    ← You are here
```

---

## The Mathematics (5 minutes)

VOID is built on **finitary mathematics** — no infinity anywhere in the system.

**Core principles:**

- **Fin type** replaces natural numbers. Bounded by axiom MAX. No infinity even at proof level.
- **Bool3**: True / False / Unknown. When budget exhausts, "unknown" is the answer — not a guess.
- **Budget + Heat = constant**. Every WRITE operation costs one tick and generates heat. Conservation law, not metaphor.
- **Ratio(n, d)** replaces floating point. Fixed denominators prevent explosion. No IEEE 754.
- **Credit propagation** replaces backpropagation. Learning = selective budget refund for accurate predictions. Failed predictions dissipate as irretrievable heat.

**Formally verified in Coq** with a single intentionally admitted axiom (MAX bound).

For the full mathematical treatment: [THEORY.md](theory/THEORY.md)

---

## Why This Exists

Current neural networks cannot say "I don't know." Softmax always produces a probability distribution. Always gives an answer. This is not a bug — it's a consequence of infinite mathematics baked into the architecture.

VOID attacks this at the foundation: finite math, finite budget, finite confidence. The system defaults to silence and must *earn* the right to speak by exceeding population-norm confidence.

A network that always answers is useful but dishonest.
A network that never answers is honest but useless.
VOID finds the boundary.

---

## Author

**Gustaw Konrad Wojnowski** — cultural theorist, theater scholar, University of Silesia.

Not a mathematician. Not a programmer.
Built this because infinity is a bug, not a feature.

---

## Citation

```
@misc{wojnowski2025void,
  author = {Wojnowski, Gustaw Konrad},
  title = {VOID Theory: Finite Mathematics for Anti-Hallucination Neural Networks},
  year = {2025},
  publisher = {GitHub},
  url = {https://github.com/probabilistic-minds-consortium/void-theory}
}
```

---

## License

MIT — Use freely, but remember: everything costs.
