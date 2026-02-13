"""
test_void_verify.py — Does this thing actually work?

Not "does it run" — does it do what VOID promises:
1. Budget always decreases (second law)
2. Heat always increases (energy conservation)
3. Budget exhaustion → "dont_know", never hallucination
4. Divergent input → rejection
5. Normal input → acceptance
6. Integer arithmetic is consistent (no overflow, no division by zero)
7. Three layers share one budget correctly
"""

import random
import sys

# We test without Phi-3. Pure logic only.
from void_in_layer import (
    Ratio, VoidInResult, VoidInPopulation,
    void_in, quantize_embedding, calculate_population_stats,
    RESOLUTION, EXISTENCE_THRESHOLD_N,
)
from void_out_layer import (
    VoidOutResult, VoidOutPopulation,
    void_out, quantize_logits_topk, compute_gap_spread,
    calculate_output_stats,
)
from void_mid_layer import (
    VoidMidGate, VoidMidPopulation, VoidMidResult,
    ratio_sub, ratio_abs, ratio_gt,
)
from void_hooked_model import quantize


passed = 0
failed = 0


def check(name: str, condition: bool, detail: str = ""):
    global passed, failed
    if condition:
        passed += 1
        print(f"  OK   {name}")
    else:
        failed += 1
        print(f"  FAIL {name}  {detail}")


# ═══════════════════════════════════════════════════════
# 1. RATIO ARITHMETIC
# ═══════════════════════════════════════════════════════
print("=== 1. Ratio Arithmetic ===")

# Subtraction
r = ratio_sub(Ratio(750, 1000), Ratio(500, 1000))
check("sub positive", r.n == 250000 and r.d == 1000000)

r = ratio_sub(Ratio(100, 1000), Ratio(900, 1000))
check("sub negative", r.n == -800000 and r.d == 1000000)

r = ratio_sub(Ratio(500, 1000), Ratio(500, 1000))
check("sub zero", r.n == 0)

# Absolute value
r = ratio_abs(Ratio(-500, 1000))
check("abs negative", r.n == 500 and r.d == 1000)

r = ratio_abs(Ratio(500, 1000))
check("abs positive", r.n == 500 and r.d == 1000)

# Greater than
check("gt true", ratio_gt(Ratio(750, 1000), Ratio(500, 1000)))
check("gt false", not ratio_gt(Ratio(500, 1000), Ratio(750, 1000)))
check("gt equal", not ratio_gt(Ratio(500, 1000), Ratio(500, 1000)))

# Cross-denominator comparison
check("gt cross-denom", ratio_gt(Ratio(3, 4), Ratio(2, 3)))  # 0.75 > 0.666


# ═══════════════════════════════════════════════════════
# 2. TRANSDUCTION BOUNDARY
# ═══════════════════════════════════════════════════════
print("\n=== 2. Transduction Boundary ===")

q = quantize_embedding([0.0, 1.0, -1.0, 0.5, -0.5])
check("quantize length", len(q) == 5)
check("quantize zero", q[0] == Ratio(0, RESOLUTION))
check("quantize one", q[1] == Ratio(1000, RESOLUTION))
check("quantize neg", q[2] == Ratio(-1000, RESOLUTION))
check("quantize half", q[3] == Ratio(500, RESOLUTION))

# All denominators must be RESOLUTION
check("quantize denom uniform", all(r.d == RESOLUTION for r in q))

# Existence threshold
check("ghost below threshold",
      abs(quantize_embedding([0.005])[0].n) < EXISTENCE_THRESHOLD_N)
check("exists above threshold",
      abs(quantize_embedding([0.05])[0].n) >= EXISTENCE_THRESHOLD_N)

# Logit quantization
indices, ratios, heat = quantize_logits_topk([1.0, 5.0, 3.0, 2.0], k=2)
check("topk finds top", indices[0] == 1, f"got {indices[0]}")
check("topk second", indices[1] == 2, f"got {indices[1]}")
check("topk sorted desc", ratios[0].n >= ratios[1].n)
check("topk heat > 0", heat > 0)


# ═══════════════════════════════════════════════════════
# 3. VOID-IN: BUDGET INVARIANTS
# ═══════════════════════════════════════════════════════
print("\n=== 3. VOID-IN Budget Invariants ===")

# Build population
random.seed(42)
fake_embs = [[random.gauss(0, 1) for _ in range(100)] for _ in range(20)]
pop_stats = calculate_population_stats(fake_embs)

fake_input = [random.gauss(0, 1) for _ in range(100)]

# Normal budget
r = void_in(fake_input, 10000, pop_stats)
check("in heat > 0", r.heat > 0)
check("in budget decreases", r.budget_remaining < 10000)
check("in heat + remaining <= budget", r.heat + r.budget_remaining <= 10000)
check("in complete", not r.incomplete)
check("in processed all", r.processed_dims == 100)

# Exact budget accounting
check("in budget exact", r.budget_remaining == 10000 - r.heat,
      f"remaining={r.budget_remaining} expected={10000 - r.heat}")

# Zero budget → incomplete
r0 = void_in(fake_input, 0, pop_stats)
check("in zero budget incomplete", r0.incomplete)
check("in zero budget no heat", r0.heat == 0)
check("in zero budget processed 0", r0.processed_dims == 0)

# Budget = 1 → processes at most 0 dims (need 2 per dim: quantize + weight)
r1 = void_in(fake_input, 1, pop_stats)
check("in budget=1 incomplete", r1.incomplete)

# Weights: all should have d=RESOLUTION
r_full = void_in(fake_input, 100000, pop_stats)
check("in weights denom", all(w.d == RESOLUTION for w in r_full.weights))
check("in embedding denom", all(e.d == RESOLUTION for e in r_full.embedding))


# ═══════════════════════════════════════════════════════
# 4. VOID-OUT: DECISION LOGIC
# ═══════════════════════════════════════════════════════
print("\n=== 4. VOID-OUT Decision Logic ===")

# Build output population
fake_logits_list = [[random.gauss(0, 1) for _ in range(1000)] for _ in range(30)]
out_stats = calculate_output_stats(fake_logits_list)
out_pop = out_stats['population']

check("out pop has samples", out_pop.n_samples == 30)
check("out pop gap_mad >= 1", out_pop.gap_mad_n >= 1)
check("out pop spread_mad >= 1", out_pop.spread_mad_n >= 1)

# Spiked logit → answer
spiked = [random.gauss(0, 1) for _ in range(1000)]
spiked[42] = 15.0
r_spike = void_out(spiked, 999999, out_stats, z_threshold_n=1000)
check("out spike = answer", r_spike.decision == "answer")
check("out spike token = 42", r_spike.top_token_id == 42, f"got {r_spike.top_token_id}")
check("out spike z_conf > threshold", r_spike.z_conf >= 1000)
check("out spike heat > 0", r_spike.heat > 0)

# Flat logits → dont_know
flat = [random.gauss(0, 0.01) for _ in range(1000)]
r_flat = void_out(flat, 999999, out_stats, z_threshold_n=1000)
check("out flat = dont_know", r_flat.decision == "dont_know")
check("out flat no token", r_flat.top_token_id == -1)

# Budget exhaustion → exhausted
r_broke = void_out(spiked, 2, out_stats, z_threshold_n=1000)
check("out broke = exhausted", r_broke.decision == "exhausted")
check("out broke no heat", r_broke.heat == 0)

# Budget accounting
r_budget = void_out(spiked, 999999, out_stats)
check("out budget exact",
      r_budget.budget_remaining == 999999 - r_budget.heat,
      f"remaining={r_budget.budget_remaining} expected={999999 - r_budget.heat}")

# Gap and spread are correct
gap_n, spread_n, _ = compute_gap_spread(r_spike.logits_quantized)
check("out gap = confidence.n", gap_n == r_spike.confidence.n)
check("out spread = entropy.n", spread_n == r_spike.entropy.n)
check("out gap >= 0 for spike", gap_n >= 0)
check("out spread >= 0 for spike", spread_n >= 0)


# ═══════════════════════════════════════════════════════
# 5. VOID-MID: GATE LOGIC
# ═══════════════════════════════════════════════════════
print("\n=== 5. VOID-MID Gate Logic ===")

# Build population
pop = VoidMidPopulation()
samples = [
    [Ratio(100, 1000), Ratio(200, 1000), Ratio(300, 1000)],
    [Ratio(110, 1000), Ratio(190, 1000), Ratio(310, 1000)],
    [Ratio(90, 1000),  Ratio(210, 1000), Ratio(290, 1000)],
    [Ratio(105, 1000), Ratio(195, 1000), Ratio(305, 1000)],
    [Ratio(95, 1000),  Ratio(205, 1000), Ratio(295, 1000)],
]
pop.build_from_samples(samples)

check("mid pop mean[0]", pop.mean[0].n == 100)
check("mid pop spread >= 1", all(s.n >= 1 for s in pop.spread))

# Normal state → continue
gate = VoidMidGate(layer_positions=[0], budget=10000)
gate.populations[0] = pop
normal = [Ratio(100, 1000), Ratio(200, 1000), Ratio(300, 1000)]
r_n = gate.evaluate(normal, 0)
check("mid normal continues", r_n.should_continue)

# Divergent state → exit
gate.reset(10000)
gate.populations[0] = pop
divergent = [Ratio(900, 1000), Ratio(-800, 1000), Ratio(900, 1000)]
r_d = gate.evaluate(divergent, 0)
check("mid divergent exits", not r_d.should_continue)

# Budget exhaustion → exit
gate.reset(1)
gate.populations[0] = pop
r_e = gate.evaluate(normal, 0)
check("mid exhausted exits", not r_e.should_continue)
check("mid exhausted reason", "budget" in r_e.reason)

# Budget tracking across multiple evaluations
gate.reset(10000)
gate.populations[0] = pop
gate.evaluate(normal, 0)
heat_after_1 = gate.total_heat
budget_after_1 = gate.budget
gate.evaluate(normal, 0)
heat_after_2 = gate.total_heat
budget_after_2 = gate.budget
check("mid heat increases", heat_after_2 > heat_after_1)
check("mid budget decreases", budget_after_2 < budget_after_1)
check("mid heat + budget = initial", gate.total_heat + gate.budget == 10000,
      f"heat={gate.total_heat} budget={gate.budget} sum={gate.total_heat + gate.budget}")


# ═══════════════════════════════════════════════════════
# 6. PIPELINE INTEGRATION (mock)
# ═══════════════════════════════════════════════════════
print("\n=== 6. Pipeline Integration ===")

from void_pipeline import void_pipeline_mock

# Build stats
random.seed(123)
dim = 64  # small for testing
vocab = 500
fake_e = [[random.gauss(0, 1) for _ in range(dim)] for _ in range(20)]
fake_l = [[random.gauss(0, 1) for _ in range(vocab)] for _ in range(20)]
p_stats = calculate_population_stats(fake_e)
o_stats = calculate_output_stats(fake_l)

# No spike → dont_know
r_ns = void_pipeline_mock("test", 999999, p_stats, o_stats,
                           embedding_dim=dim, vocab_size=vocab)
check("pipe no-spike = dont_know", r_ns.decision in ["dont_know", "exhausted"])
check("pipe heat > 0", r_ns.total_heat > 0)
check("pipe budget accounting",
      r_ns.total_heat + r_ns.budget_remaining <= 999999,
      f"heat={r_ns.total_heat} rem={r_ns.budget_remaining}")

# Spike → answer
r_sp = void_pipeline_mock("test", 999999, p_stats, o_stats,
                           embedding_dim=dim, vocab_size=vocab, spike_token=42)
check("pipe spike = answer", r_sp.decision == "answer")

# Tiny budget → exhausted
r_tiny = void_pipeline_mock("test", 1, p_stats, o_stats,
                             embedding_dim=dim, vocab_size=vocab)
check("pipe tiny = exhausted", r_tiny.decision == "exhausted")

# With mid-gate
gate = VoidMidGate(layer_positions=[0, 1], budget=50000)
for pos in [0, 1]:
    mp = VoidMidPopulation()
    s = [[Ratio(int(random.gauss(0, 1) * 1000), 1000) for _ in range(64)]
         for _ in range(10)]
    mp.build_from_samples(s)
    gate.populations[pos] = mp

r_mid = void_pipeline_mock("test", 999999, p_stats, o_stats,
                            mid_gate=gate, embedding_dim=dim, vocab_size=vocab)
check("pipe mid has results", len(r_mid.mid_results) > 0)
check("pipe mid budget accounting",
      r_mid.total_heat + r_mid.budget_remaining <= 999999)


# ═══════════════════════════════════════════════════════
# 7. STRESS: SECOND LAW (heat never decreases)
# ═══════════════════════════════════════════════════════
print("\n=== 7. Second Law Stress Test ===")

random.seed(999)
violations = 0
for trial in range(100):
    budget = random.randint(1, 100000)
    fake = [random.gauss(0, 1) for _ in range(100)]
    r = void_in(fake, budget, p_stats)
    if r.heat < 0:
        violations += 1
    if r.budget_remaining > budget:
        violations += 1
    if r.heat + r.budget_remaining > budget:
        violations += 1

check(f"second law IN (100 trials)", violations == 0, f"{violations} violations")

violations = 0
for trial in range(100):
    budget = random.randint(1, 100000)
    fake = [random.gauss(0, 1) for _ in range(vocab)]
    r = void_out(fake, budget, o_stats)
    if r.heat < 0:
        violations += 1
    if r.budget_remaining > budget:
        violations += 1
    if r.heat + r.budget_remaining > budget:
        violations += 1

check(f"second law OUT (100 trials)", violations == 0, f"{violations} violations")


# ═══════════════════════════════════════════════════════
# 8. EDGE: EXTREME VALUES
# ═══════════════════════════════════════════════════════
print("\n=== 8. Extreme Values ===")

# Very large float
q_big = quantize_embedding([1e10])
check("quantize huge", q_big[0].d == RESOLUTION)  # doesn't crash

# Very small float
q_tiny = quantize_embedding([1e-10])
check("quantize tiny = ghost", abs(q_tiny[0].n) < EXISTENCE_THRESHOLD_N)

# Negative huge
q_neg = quantize_embedding([-1e10])
check("quantize neg huge", q_neg[0].n < 0)

# All zeros
r_zeros = void_in([0.0] * 100, 10000, p_stats)
check("in all zeros complete", not r_zeros.incomplete)
check("in all zeros = ghosts", all(w.n == 0 for w in r_zeros.weights))

# Identical logits (maximum entropy)
identical = [1.0] * vocab
r_id = void_out(identical, 999999, o_stats)
check("out identical = dont_know", r_id.decision == "dont_know")
check("out identical gap = 0", r_id.confidence.n == 0)


# ═══════════════════════════════════════════════════════
# SUMMARY
# ═══════════════════════════════════════════════════════
print(f"\n{'=' * 50}")
print(f"  PASSED: {passed}")
print(f"  FAILED: {failed}")
print(f"{'=' * 50}")

if failed > 0:
    sys.exit(1)
