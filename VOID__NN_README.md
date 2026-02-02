# VOID Neural Network

## Finite Mathematics for Pattern Recognition

> *"The decimal point is just notation. IEEE 754 is the heresy."*

---

## What is VOID?

VOID is a neural network architecture built on **strictly finite mathematics**. No floating-point infinity. No hidden theological assumptions. Every operation costs **budget**, and when budget runs out, the network says **"I don't know"** instead of hallucinating an answer.

This is pattern recognition the way Maat would approve — honest about its limits.

---

## Core Principles

### 1. Budget = Mortality
Every observation costs. The network has finite resources. It dies before seeing everything — just like any real observer.

```
Test 7: asthma
Budget spent: 77,324 operations
Remaining: 22,676
```

### 2. Ratio, Not Float
Confidence is not `0.625`. It's `5/8`. 

```
"0.625" → 625/1000 → simplified: 5/8 = 62.5%
```

All comparisons use **cross-multiplication** (`a/b ≥ c/d ⟺ a×d ≥ c×b`). Division only happens at the final display for human eyes.

### 3. "I Don't Know" Is Valid
When no pattern exceeds the confidence threshold, the network admits uncertainty instead of forcing a match.

```
Test 4: Looking for 'ADHD'
  → I DON'T KNOW (checked 203 patterns)
  → This is honest - no confident match found
```

### 4. Entropy-Weighted Resonance
Rare symptoms carry more information than common ones. "Hemoptysis" matters more than "cough".

```
RAREST symptoms (weight=100,000):
  - symptom[20], symptom[34], symptom[38]
  
COMMON symptoms (weight=8,000):
  - symptom[47] (appears in 24/200 patterns)
```

---

## Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                    VOID NETWORK v0.4                        │
│                  "True Finite" Architecture                 │
└─────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────┐
│  LAYER 1: TRANSDUCTION                                      │
│  ─────────────────────                                      │
│  Input symptoms → Binary pattern                            │
│  Cost: 1 budget                                             │
└─────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────┐
│  LAYER 2: WORKING MEMORY (Orbits)          [CHEAP PATH]     │
│  ────────────────────────────────                           │
│  7 hot patterns from recent matches                         │
│  Cost: ~377 budget per orbit checked                        │
│                                                             │
│  ┌───────┐ ┌───────┐ ┌───────┐ ┌───────┐                   │
│  │asthma │ │dental │ │corneal│ │kidney │ ...               │
│  │ 0/3   │ │ 0/9   │ │ 0/1   │ │ 1/1   │                   │
│  └───────┘ └───────┘ └───────┘ └───────┘                   │
└─────────────────────────────────────────────────────────────┘
                              │
                    (if no orbit match)
                              ▼
┌─────────────────────────────────────────────────────────────┐
│  LAYER 3: MEMORY BANK                      [EXPENSIVE PATH] │
│  ────────────────────                                       │
│  200 patterns × 377 symptoms                                │
│  Cost: ~75,000 budget for full scan                         │
│                                                             │
│  Entropy-weighted Jaccard similarity:                       │
│  confidence = Σ(weight × match) / Σ(weight × union)         │
└─────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────┐
│  LAYER 4: ECONOMY                                           │
│  ────────────────                                           │
│  • Promote strong matches to orbits                         │
│  • Demote weak orbits (strength < 30%)                      │
│  • Cost: 10 budget per promotion                            │
└─────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────┐
│  OUTPUT                                                     │
│  ──────                                                     │
│  • Match:     { diagnosis, confidence: Ratio, budget }      │
│  • DontKnow:  { patterns_checked, budget }                  │
│  • Exhausted: { partial_best, budget }                      │
└─────────────────────────────────────────────────────────────┘
```

---

## Results (Medical Diagnosis)

Tested on 1,179 diseases with 377 binary symptoms.

| Test | Target | Result | Confidence |
|------|--------|--------|------------|
| 1 | dental caries | ✓ CORRECT | 168570/240322 = 70.1% |
| 2 | thrombophlebitis | ✓ CORRECT | 193181/276746 = 69.8% |
| 3 | spondylosis | → degenerative disc | 142941/211353 = 67.6% |
| 4 | ADHD | **I DON'T KNOW** | — |
| 5 | mitral valve disease | ✓ CORRECT | 122500/214245 = 57.1% |
| 6 | vaginitis | **I DON'T KNOW** | — |
| 7 | asthma | ✓ CORRECT | 79363/120796 = 65.7% |
| 8 | cellulitis of mouth | **I DON'T KNOW** | — |
| 9 | corneal disorder | ✓ CORRECT | 151513/210097 = 72.1% |
| 10 | pyelonephritis | → kidney stone | 109482/189912 = 57.6% |

**5 correct, 2 wrong (medically related), 3 honest "I don't know"**

---

## The Ontological Fix

Traditional neural networks hide infinity in IEEE 754 floats:

```
0.1 + 0.2 = 0.30000000000000004  ← HERESY
```

VOID uses **Ratio arithmetic**:

```rust
pub struct Ratio {
    n: u32,  // numerator
    d: u32,  // denominator
}

// "0.5" parsed directly to integers
Ratio::from_decimal_str("0.5") → Ratio { n: 5, d: 10 }

// Comparison via cross-multiplication (NO DIVISION!)
// a/b ≥ c/d  ⟺  a×d ≥ c×b
fn ge(&self, other: &Ratio) -> bool {
    self.n * other.d >= other.n * self.d
}
```

---

## Philosophy

VOID emerges from a critique of Pascal's Wager: the hidden assumption that infinite reward makes finite cost irrelevant. This theological contraband infected mathematics through Cantor's infinities and persists in every IEEE 754 float.

VOID asks: **What if observation itself costs?**

- Budget enforces mortality
- Heat tracks irreversibility  
- Ratio preserves finite arithmetic
- "I don't know" respects epistemic limits

The network doesn't pretend to be an omniscient narrator. It's a finite observer that dies before seeing everything.

---

## Usage

```bash
cd void_network_v4
cargo run --release
```

```rust
let mut network = VoidNetwork::new();
network.load_patterns_free(training_data);

let budget = Budget::new(100_000);
let result = network.infer(symptoms, budget);

match result {
    InferenceResult::Match { diagnosis, confidence, .. } => {
        println!("{}: {}", diagnosis, confidence.to_percent_string(1));
    }
    InferenceResult::DontKnow { .. } => {
        println!("Insufficient evidence for diagnosis");
    }
    InferenceResult::Exhausted { .. } => {
        println!("Budget depleted before conclusion");
    }
}
```

---

## Files

- `main.rs` — 550 lines, complete implementation
- `disease_symptoms_sample.csv` — 1,179 diseases × 377 symptoms

---

## Credits

Developed through adversarial collaboration between human (Gustaw) and AI (Claude + Gemini).

Gemini caught the ontological leaks. Claude wrote the code. Gustaw refused to let Pascal win.

---

*Maat weighs ratios. Pascal's floats can go to hell.*
