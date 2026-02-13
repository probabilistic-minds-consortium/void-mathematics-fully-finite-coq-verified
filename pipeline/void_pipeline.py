"""
void_pipeline.py - VOID Pipeline v3.1 (Three-Layer Integration, Float-Free)

Input → Tokenizer → Phi-3 → VOID-IN → Phi-3 Layers (VOID-MID) → VOID-OUT → Decision

Three layers, ONE budget. Heat is universal currency.
IN spends budget perceiving. MID spends budget monitoring. OUT spends budget deciding.
If any layer exhausts the shared budget, everything downstream stops.

BUDGET MODEL:
  VOID counts the cost of its OWN operations only.
  The LLM forward pass is an operation of the EXTERNAL WORLD.
  We do not count what we cannot control.
  COST_FORWARD = 1 tick means "one invocation of the oracle."
  This is a deliberate choice, not an oversight.

"I don't know" can come from any gate:
  - IN: "couldn't finish perceiving" (incomplete)
  - MID: "hidden states diverged" or "no budget left" (early exit)
  - OUT: "not confident enough" (dont_know)

No floats in VOID logic. Transduction boundaries at IN and OUT edges only.
"""

from typing import Optional, List, NamedTuple

try:
    import torch
    HAS_TORCH = True
except ImportError:
    HAS_TORCH = False

from void_in_layer import (
    Ratio, VoidInResult, VoidInPopulation,
    void_in, calculate_population_stats, quantize_embedding,
)
from void_out_layer import (
    VoidOutResult, VoidOutPopulation,
    void_out, calculate_output_stats, quantize_logits_topk,
)
from void_mid_layer import VoidMidGate, VoidMidPopulation, VoidMidResult
from void_hooked_model import VoidHookedModel, quantize


class VoidPipelineResult(NamedTuple):
    decision: str              # "answer" | "dont_know" | "exhausted" | "mid_exit"
    response: Optional[str]
    void_in_result: VoidInResult
    mid_results: List[VoidMidResult]
    void_out_result: Optional[VoidOutResult]
    total_heat: int
    budget_remaining: int
    exit_source: str           # "in" | "mid" | "out" | "budget" | "ok"


# ── Budget model ──
# These are costs of INVOKING the external oracle (LLM).
# They are deliberately low because we don't count the oracle's
# internal cost — we count the cost of our decision to invoke it.
COST_TOKENIZE = 1     # one invocation: "make tokens"
COST_FORWARD = 1      # one invocation: "run the oracle"


def build_population_stats(prompts, model, tokenizer, mid_gate: Optional[VoidMidGate] = None):
    """
    Build ALL population statistics from calibration prompts.

    TRANSDUCTION happens here: we extract floats from Phi-3
    and pass them through the quantization boundary ONCE.

    Returns:
        (population_stats, output_stats)
        Side effect: mid_gate.populations populated if mid_gate given.
    """
    embeddings_float = []
    logits_float = []

    for prompt in prompts:
        inputs = tokenizer(prompt, return_tensors="pt")
        with torch.no_grad():
            outputs = model(**inputs, output_hidden_states=True)

        emb = outputs.hidden_states[1][0, -1, :].cpu().numpy()
        lgts = outputs.logits[0, -1, :].cpu().numpy()

        embeddings_float.append(emb)
        logits_float.append(lgts)

    # Both functions handle transduction internally
    # (quantize first, then compute integer stats)
    population_stats = calculate_population_stats(embeddings_float)
    output_stats = calculate_output_stats(logits_float)

    # Calibrate mid-layer if gate provided
    if mid_gate is not None:
        hooked = VoidHookedModel(model, tokenizer, mid_gate)
        hooked.calibrate(prompts)

    return population_stats, output_stats


def void_pipeline(
    text: str,
    budget: int,
    model,
    tokenizer,
    population_stats: dict,
    output_stats: dict,
    mid_gate: Optional[VoidMidGate] = None,
    z_threshold_n: int = 1000,    # integer z-threshold (1000 = 1.0 z-scores)
) -> VoidPipelineResult:
    """
    Full VOID pipeline with three-layer integration.

    Budget is SHARED across all layers:
      1. IN consumes budget perceiving embeddings
      2. MID consumes budget monitoring hidden states (via hooks)
      3. OUT consumes budget deciding on logits

    If mid_gate is None, behaves like v2 (IN + OUT only).

    z_threshold_n is in RESOLUTION units: 1000 = 1.0 z-scores.
    """
    total_heat = 0
    mid_results = []

    # ── 0. MINIMUM COST CHECK ────────────────────────
    if budget < COST_TOKENIZE + COST_FORWARD:
        empty_in = VoidInResult([], [], 0, budget, True, 0)
        return VoidPipelineResult(
            "exhausted", None, empty_in, [], None, 0, budget, "budget",
        )

    # ── 1. TOKENIZE (oracle invocation) ──────────────
    inputs = tokenizer(text, return_tensors="pt")
    total_heat += COST_TOKENIZE
    budget -= COST_TOKENIZE

    # ── 2. INSTALL MID-LAYER HOOKS ───────────────────
    hooked = None
    if mid_gate is not None:
        mid_gate.reset(budget=budget // 3)
        hooked = VoidHookedModel(model, tokenizer, mid_gate)
        hooked.install_hooks()

    # ── 3. PHI-3 FORWARD (oracle invocation, mid hooks fire) ──
    try:
        with torch.no_grad():
            outputs = model(**inputs, output_hidden_states=True)
    finally:
        if hooked is not None:
            hooked.remove_hooks()

    total_heat += COST_FORWARD
    budget -= COST_FORWARD

    # ── 4. COLLECT MID-LAYER RESULTS ─────────────────
    if mid_gate is not None:
        mid_results = list(mid_gate.results)
        mid_heat = mid_gate.total_heat
        total_heat += mid_heat
        budget -= mid_heat

        if mid_gate.should_exit:
            # Mid-layer said stop. Run IN for diagnostics, skip OUT.
            embedding_float = outputs.hidden_states[1][0, -1, :].cpu().numpy()
            void_in_result = void_in(embedding_float, budget, population_stats)
            total_heat += void_in_result.heat
            budget -= void_in_result.heat

            return VoidPipelineResult(
                decision="mid_exit",
                response=None,
                void_in_result=void_in_result,
                mid_results=mid_results,
                void_out_result=None,
                total_heat=total_heat,
                budget_remaining=budget,
                exit_source="mid",
            )

    # ── Extract float tensors (still at transduction boundary) ──
    embedding_float = outputs.hidden_states[1][0, -1, :].cpu().numpy()
    logits_float = outputs.logits[0, -1, :].cpu().numpy()

    # ── 5. VOID-IN (transduction + integer perception) ──
    void_in_result = void_in(embedding_float, budget, population_stats)
    total_heat += void_in_result.heat
    budget -= void_in_result.heat

    if void_in_result.incomplete:
        return VoidPipelineResult(
            "exhausted", None, void_in_result, mid_results, None,
            total_heat, budget, "in",
        )

    # ── 6. VOID-OUT (transduction + integer decision) ──
    void_out_result = void_out(logits_float, budget, output_stats, z_threshold_n)
    total_heat += void_out_result.heat
    budget -= void_out_result.heat

    # ── 7. DECISION ──────────────────────────────────
    if void_out_result.decision == "answer":
        response = tokenizer.decode(
            [void_out_result.top_token_id],
            skip_special_tokens=True,
        )
    else:
        response = None

    return VoidPipelineResult(
        decision=void_out_result.decision,
        response=response,
        void_in_result=void_in_result,
        mid_results=mid_results,
        void_out_result=void_out_result,
        total_heat=total_heat,
        budget_remaining=budget,
        exit_source="out" if void_out_result.decision != "answer" else "ok",
    )


# ═══════════════════════════════════════════════════════
# MOCK MODE (no model required)
# ═══════════════════════════════════════════════════════

def void_pipeline_mock(
    text: str,
    budget: int,
    population_stats: dict,
    output_stats: dict,
    mid_gate: Optional[VoidMidGate] = None,
    z_threshold_n: int = 1000,
    embedding_dim: int = 3072,
    vocab_size: int = 32064,
    spike_token: int = -1,
) -> VoidPipelineResult:
    """
    Test pipeline with synthetic data. No model required.
    Uses random module for synthetic data (NOT in VOID logic path).
    """
    import random

    total_heat = 0
    mid_results = []

    if budget < COST_TOKENIZE + COST_FORWARD:
        empty_in = VoidInResult([], [], 0, budget, True, 0)
        return VoidPipelineResult(
            "exhausted", None, empty_in, [], None, 0, budget, "budget",
        )

    total_heat += COST_TOKENIZE + COST_FORWARD
    budget -= COST_TOKENIZE + COST_FORWARD

    seed = hash(text) % (2**31)
    rng = random.Random(seed)

    # ── MID-LAYER (mock: synthetic hidden states) ────
    if mid_gate is not None:
        mid_gate.reset(budget=budget // 3)
        for pos in mid_gate.layer_positions:
            fake_hidden = [rng.gauss(0, 1) for _ in range(64)]
            ratios = quantize(fake_hidden)
            result = mid_gate.evaluate(ratios, pos)
            mid_results.append(result)

        mid_heat = mid_gate.total_heat
        total_heat += mid_heat
        budget -= mid_heat

        if mid_gate.should_exit:
            empty_in = VoidInResult([], [], 0, budget, True, 0)
            return VoidPipelineResult(
                "mid_exit", None, empty_in, mid_results, None,
                total_heat, budget, "mid",
            )

    # ── Synthetic float data (at transduction boundary) ──
    fake_embedding = [rng.gauss(0, 1) for _ in range(embedding_dim)]
    fake_logits = [rng.gauss(0, 1) for _ in range(vocab_size)]
    if spike_token >= 0:
        fake_logits[spike_token] = 12.0

    # ── IN ──
    void_in_result = void_in(fake_embedding, budget, population_stats)
    total_heat += void_in_result.heat
    budget -= void_in_result.heat

    if void_in_result.incomplete:
        return VoidPipelineResult(
            "exhausted", None, void_in_result, mid_results, None,
            total_heat, budget, "in",
        )

    # ── OUT ──
    void_out_result = void_out(fake_logits, budget, output_stats, z_threshold_n)
    total_heat += void_out_result.heat
    budget -= void_out_result.heat

    if void_out_result.decision == "answer":
        response = "[token_%d]" % void_out_result.top_token_id
    else:
        response = None

    return VoidPipelineResult(
        decision=void_out_result.decision,
        response=response,
        void_in_result=void_in_result,
        mid_results=mid_results,
        void_out_result=void_out_result,
        total_heat=total_heat,
        budget_remaining=budget,
        exit_source="out" if void_out_result.decision != "answer" else "ok",
    )


# ═══════════════════════════════════════════════════════
# SELF-TEST
# ═══════════════════════════════════════════════════════

if __name__ == "__main__":
    import random
    from void_mid_layer import VoidMidPopulation, RESOLUTION

    random.seed(42)
    dim = 3072
    vocab = 32064

    # Build fake population stats (using transduction path)
    print("=== Building population stats (integer only) ===")
    fake_embs = [[random.gauss(0, 1) for _ in range(dim)] for _ in range(50)]
    fake_lgts = [[random.gauss(0, 1) for _ in range(vocab)] for _ in range(50)]

    pop_stats = calculate_population_stats(fake_embs)
    out_stats = calculate_output_stats(fake_lgts)

    in_pop = pop_stats['population']
    out_pop = out_stats['population']
    print(f"  IN:  {in_pop.n_samples} samples, {in_pop.dims} dims")
    print(f"  OUT: gap_mean={out_pop.gap_mean_n}/{RESOLUTION}  "
          f"spread_mean={out_pop.spread_mean_n}/{RESOLUTION}")

    # Build mid-layer population
    gate = VoidMidGate(layer_positions=[8, 16, 24], budget=50000)
    for pos in [8, 16, 24]:
        pop = VoidMidPopulation()
        samples = []
        for _ in range(20):
            vals = [random.gauss(0, 1) for _ in range(64)]
            samples.append(quantize(vals))
        pop.build_from_samples(samples)
        gate.populations[pos] = pop

    print()
    print("=== VOID Pipeline v3.1 — Three-Layer Integration ===")
    print()

    # Test 1: normal (no spike → should be dont_know)
    r1 = void_pipeline_mock("What is 2+2?", 500000, pop_stats, out_stats, mid_gate=gate)
    print("Test 1 (normal, no spike):")
    print(f"  decision={r1.decision}  exit_source={r1.exit_source}  "
          f"heat={r1.total_heat}  mid_checks={len(r1.mid_results)}")
    for mr in r1.mid_results:
        print(f"    L{mr.layer_index}: continue={mr.should_continue} "
              f"conf={mr.confidence_n}/{RESOLUTION} div={mr.divergence_n}/{RESOLUTION}")
    print()

    # Test 2: spiked (confident)
    gate_2 = VoidMidGate(layer_positions=[8, 16, 24], budget=50000)
    for pos in [8, 16, 24]:
        gate_2.populations[pos] = gate.populations[pos]
    r2 = void_pipeline_mock("What is 2+2?", 500000, pop_stats, out_stats,
                             mid_gate=gate_2, spike_token=1000)
    print("Test 2 (spiked token 1000):")
    print(f"  decision={r2.decision}  exit_source={r2.exit_source}  heat={r2.total_heat}")
    if r2.void_out_result:
        vo = r2.void_out_result
        print(f"  gap={vo.confidence.n}/{vo.confidence.d}  "
              f"z_conf={vo.z_conf}/{RESOLUTION}  z_entr={vo.z_entr}/{RESOLUTION}")
    print()

    # Test 3: tiny budget (should exhaust)
    gate_3 = VoidMidGate(layer_positions=[8, 16, 24], budget=50000)
    for pos in [8, 16, 24]:
        gate_3.populations[pos] = gate.populations[pos]
    r3 = void_pipeline_mock("What is 2+2?", 5, pop_stats, out_stats, mid_gate=gate_3)
    print("Test 3 (tiny budget):")
    print(f"  decision={r3.decision}  exit_source={r3.exit_source}")
    print()

    # Test 4: without mid-gate (backward compat)
    r4 = void_pipeline_mock("What is 2+2?", 500000, pop_stats, out_stats, mid_gate=None)
    print("Test 4 (no mid-gate):")
    print(f"  decision={r4.decision}  exit_source={r4.exit_source}  "
          f"mid_checks={len(r4.mid_results)}")
    print()

    print("=== All three layers share one budget. Heat is universal. ===")
    print("=== No floats in VOID logic. Transduction at the boundary. ===")
