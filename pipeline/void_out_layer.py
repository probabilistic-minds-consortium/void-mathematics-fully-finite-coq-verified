"""
void_out_layer.py - VOID-OUT Layer v3.0 (Decision Boundary)

Pure integer logic after transduction. No numpy. No softmax. No log. No exp.
Follows void_mid_layer.py standard: Ratio(n, d), MAD, integer z-scores.

Confidence = gap between top-1 and top-2 logits.
    Large gap → model is sure about one token.
    Small gap → model is torn between options.

Entropy proxy = spread of top-k logits.
    Wide spread → probability mass concentrated (low entropy).
    Narrow spread → probability mass diffuse (high entropy).

Both are pure integer. No softmax needed. No log needed.
softmax is a lie: it normalizes away the information we need.

Population baseline: "confident" means MORE confident than typical.
z-scores computed as integer deviation / MAD, exactly like void_mid_layer.py.

"A network that always says 'dont_know' is honest but useless.
 A network that always says 'answer' is useful but dishonest.
 Calibration against population finds the boundary."
"""

from typing import List, NamedTuple


class Ratio(NamedTuple):
    n: int
    d: int


class VoidOutResult(NamedTuple):
    decision: str              # "answer" | "dont_know" | "exhausted"
    top_token_id: int          # argmax token (-1 if no answer)
    confidence: Ratio          # gap top1-top2 as Ratio
    entropy: Ratio             # spread of top-k as Ratio
    z_conf: int                # z-score of confidence vs population (n/RESOLUTION)
    z_entr: int                # z-score of entropy vs population (n/RESOLUTION, inverted)
    logits_quantized: List[Ratio]
    heat: int
    budget_remaining: int
    reason: str


# ── constants ──
RESOLUTION = 1000
TOP_K = 32
COST_QUANTIZE = 1     # quantize one logit
COST_COMPARE = 1      # one comparison operation
COST_SORT_TICK = 1    # one comparison in sort


class VoidOutPopulation:
    """
    Population statistics for output logit patterns.
    Stored as integers. Computed from integers. No floats ever.
    Mirrors VoidMidPopulation from void_mid_layer.py.

    Tracks two metrics:
      - gap: top1 - top2 logit (confidence signal)
      - spread: top1 - topK logit (entropy proxy)
    """
    def __init__(self):
        self.gap_mean_n: int = 0       # mean gap numerator (d=RESOLUTION)
        self.gap_mad_n: int = 1        # MAD of gap (d=RESOLUTION, floor=1)
        self.spread_mean_n: int = 0    # mean spread numerator
        self.spread_mad_n: int = 1     # MAD of spread
        self.n_samples: int = 0

    def build_from_samples(self, samples: list):
        """
        Build population from list of (gap_n, spread_n) integer pairs.
        All values are numerators with d=RESOLUTION.

        Args:
            samples: list of (gap_n: int, spread_n: int) tuples
        """
        if not samples:
            return

        self.n_samples = len(samples)
        n = self.n_samples

        gaps = [s[0] for s in samples]
        spreads = [s[1] for s in samples]

        # Mean (integer)
        self.gap_mean_n = sum(gaps) // n
        self.spread_mean_n = sum(spreads) // n

        # MAD (integer, floor at 1)
        self.gap_mad_n = max(1, sum(abs(g - self.gap_mean_n) for g in gaps) // n)
        self.spread_mad_n = max(1, sum(abs(s - self.spread_mean_n) for s in spreads) // n)


def quantize_logits_topk(logits_float, k: int = TOP_K) -> tuple:
    """
    TRANSDUCTION BOUNDARY for logits. Float dies here.

    Quantizes ALL logits to integer, then finds top-k by integer comparison.
    Returns (top_k_indices, top_k_ratios, heat).

    This is O(vocab) for the initial scan — we must touch every logit once
    to find the top-k. Each touch costs one tick.

    Args:
        logits_float: iterable of floats (numpy array ok at boundary)
        k: how many top logits to keep

    Returns:
        (indices: List[int], ratios: List[Ratio], heat: int)
    """
    heat = 0

    # ── TRANSDUCTION: float → int, find top-k in one pass ──
    # We maintain a list of k largest (index, numerator) pairs.
    # This is a selection algorithm, not a full sort.
    topk = []  # list of (index, n) sorted descending by n
    min_in_topk = None  # smallest n currently in topk

    vocab_size = len(logits_float) if hasattr(logits_float, '__len__') else 0

    for i in range(vocab_size):
        n = int(round(float(logits_float[i]) * RESOLUTION))
        heat += COST_QUANTIZE

        if len(topk) < k:
            topk.append((i, n))
            heat += COST_COMPARE
            if min_in_topk is None or n < min_in_topk:
                min_in_topk = n
        elif n > min_in_topk:
            # Replace the minimum element
            # Find min index (costs comparisons)
            min_idx = 0
            for j in range(1, len(topk)):
                heat += COST_COMPARE
                if topk[j][1] < topk[min_idx][1]:
                    min_idx = j
            topk[min_idx] = (i, n)
            # Update min_in_topk
            min_in_topk = min(t[1] for t in topk)
            heat += COST_COMPARE
        # else: not in top-k, skip (but quantization already cost a tick)

    # Sort top-k descending (small sort, costs k*log(k) comparisons)
    for i in range(len(topk)):
        for j in range(i + 1, len(topk)):
            heat += COST_SORT_TICK
            if topk[j][1] > topk[i][1]:
                topk[i], topk[j] = topk[j], topk[i]

    indices = [t[0] for t in topk]
    ratios = [Ratio(t[1], RESOLUTION) for t in topk]

    return indices, ratios, heat


def compute_gap_spread(topk_ratios: List[Ratio]) -> tuple:
    """
    Compute confidence (gap) and entropy proxy (spread) from sorted top-k.
    Pure integer. Two ticks of heat.

    gap = top1.n - top2.n (higher = more confident)
    spread = top1.n - topK.n (higher = more concentrated = lower entropy)

    Returns: (gap_n: int, spread_n: int, heat: int)
    """
    if len(topk_ratios) < 2:
        return 0, 0, 0

    gap_n = topk_ratios[0].n - topk_ratios[1].n
    spread_n = topk_ratios[0].n - topk_ratios[-1].n
    heat = 2 * COST_COMPARE  # two subtractions
    return gap_n, spread_n, heat


def calculate_output_stats(logits_float_list) -> dict:
    """
    Build population statistics from float logits.

    TRANSDUCTION: quantizes all logits to Ratio FIRST,
    then computes stats in pure integer arithmetic.

    Args:
        logits_float_list: list of float arrays (from Phi-3 calibration)

    Returns:
        dict with 'population' (VoidOutPopulation)
    """
    samples = []
    for logits_float in logits_float_list:
        _indices, topk_ratios, _heat = quantize_logits_topk(logits_float, TOP_K)
        gap_n, spread_n, _h = compute_gap_spread(topk_ratios)
        samples.append((gap_n, spread_n))

    pop = VoidOutPopulation()
    pop.build_from_samples(samples)

    return {
        'population': pop,
    }


def void_out(
    logits_float,
    budget: int,
    output_stats: dict,
    z_threshold_n: int = 1000,    # threshold in RESOLUTION units (1000 = 1.0 z-score)
) -> VoidOutResult:
    """
    Quantize top-k logits, compute gap/spread, decide via integer z-scores.

    Args:
        logits_float: shape (vocab_size,), any numeric iterable
        budget: remaining operations
        output_stats: from calculate_output_stats()
        z_threshold_n: how many z-score units (n/RESOLUTION) above population
                       1000 = 1.0 standard deviations

    Returns:
        VoidOutResult with population-relative decision

    TRANSDUCTION: float→Ratio happens once during quantize_logits_topk.
    All decisions after that are pure integer.
    """
    heat = 0

    # ── Minimum cost check ──
    # Need at least: 2 logits quantized + 2 comparisons
    min_cost = 2 * COST_QUANTIZE + 2 * COST_COMPARE
    if budget < min_cost:
        return VoidOutResult(
            decision="exhausted",
            top_token_id=-1,
            confidence=Ratio(0, RESOLUTION),
            entropy=Ratio(0, RESOLUTION),
            z_conf=0,
            z_entr=0,
            logits_quantized=[],
            heat=0,
            budget_remaining=budget,
            reason="budget exhausted before decision",
        )

    # ── 1. TRANSDUCTION + TOP-K (float dies here) ──
    indices, topk_ratios, quant_heat = quantize_logits_topk(logits_float, TOP_K)
    heat += quant_heat

    if budget - heat < 4 * COST_COMPARE:
        # Not enough for gap + spread + 2 z-scores
        return VoidOutResult(
            decision="exhausted",
            top_token_id=-1,
            confidence=Ratio(0, RESOLUTION),
            entropy=Ratio(0, RESOLUTION),
            z_conf=0,
            z_entr=0,
            logits_quantized=topk_ratios,
            heat=heat,
            budget_remaining=budget - heat,
            reason="budget exhausted during quantization",
        )

    # ── 2. GAP + SPREAD (pure integer) ──
    gap_n, spread_n, gs_heat = compute_gap_spread(topk_ratios)
    heat += gs_heat

    confidence = Ratio(gap_n, RESOLUTION)
    entropy = Ratio(spread_n, RESOLUTION)

    # ── 3. Z-SCORES vs population (pure integer) ──
    pop = output_stats['population']

    # z_conf = (gap - pop_mean_gap) * RESOLUTION / pop_mad_gap
    z_conf = ((gap_n - pop.gap_mean_n) * RESOLUTION) // pop.gap_mad_n
    heat += COST_COMPARE

    # z_entr = (spread - pop_mean_spread) * RESOLUTION / pop_mad_spread
    # Higher spread = lower entropy = MORE confident → same sign as z_conf
    z_entr = ((spread_n - pop.spread_mean_n) * RESOLUTION) // pop.spread_mad_n
    heat += COST_COMPARE

    # ── 4. DECISION (integer comparison) ──
    if z_conf >= z_threshold_n and z_entr >= z_threshold_n:
        decision = "answer"
        top_token_id = indices[0] if indices else -1
        reason = (f"z_conf={z_conf}/{RESOLUTION} z_entr={z_entr}/{RESOLUTION} "
                  f"threshold={z_threshold_n}/{RESOLUTION}")
    else:
        decision = "dont_know"
        top_token_id = -1
        parts = []
        if z_conf < z_threshold_n:
            parts.append(f"z_conf={z_conf}/{RESOLUTION} < {z_threshold_n}/{RESOLUTION}")
        if z_entr < z_threshold_n:
            parts.append(f"z_entr={z_entr}/{RESOLUTION} < {z_threshold_n}/{RESOLUTION}")
        reason = ", ".join(parts)

    return VoidOutResult(
        decision=decision,
        top_token_id=top_token_id,
        confidence=confidence,
        entropy=entropy,
        z_conf=z_conf,
        z_entr=z_entr,
        logits_quantized=topk_ratios,
        heat=heat,
        budget_remaining=budget - heat,
        reason=reason,
    )


# ─────────────────────────────────────────────────────────
if __name__ == "__main__":
    print("=== VOID-OUT: Pure Integer Test ===")
    print()

    # ── Build population from synthetic data ──
    # Simulate 50 calibration logit vectors (just need top-k patterns)
    import random
    random.seed(42)
    vocab = 32064

    print("  Building population (integer only)...")
    cal_logits = []
    for _ in range(50):
        # Random logits as integers (simulating quantized)
        fake = [random.gauss(0, 1) for _ in range(vocab)]
        cal_logits.append(fake)

    ostats = calculate_output_stats(cal_logits)
    pop = ostats['population']
    print(f"    {pop.n_samples} samples")
    print(f"    Gap:    mean={pop.gap_mean_n}/{RESOLUTION}  "
          f"MAD={pop.gap_mad_n}/{RESOLUTION}")
    print(f"    Spread: mean={pop.spread_mean_n}/{RESOLUTION}  "
          f"MAD={pop.spread_mad_n}/{RESOLUTION}")
    print()

    # ── Test: spiked logit (confident) ──
    spiked = [random.gauss(0, 1) for _ in range(vocab)]
    spiked[1000] = 12.0  # one token dominates
    r1 = void_out(spiked, 999999, ostats)
    print("  SPIKED (token 1000 = 12.0):")
    print(f"    decision:  {r1.decision}")
    print(f"    token:     {r1.top_token_id}")
    print(f"    gap:       {r1.confidence.n}/{r1.confidence.d}")
    print(f"    spread:    {r1.entropy.n}/{r1.entropy.d}")
    print(f"    z_conf:    {r1.z_conf}/{RESOLUTION}")
    print(f"    z_entr:    {r1.z_entr}/{RESOLUTION}")
    print(f"    heat:      {r1.heat}")
    print(f"    reason:    {r1.reason}")
    print()

    # ── Test: flat logits (uncertain) ──
    flat = [random.gauss(0, 0.1) for _ in range(vocab)]
    r2 = void_out(flat, 999999, ostats)
    print("  FLAT (std=0.1):")
    print(f"    decision:  {r2.decision}")
    print(f"    gap:       {r2.confidence.n}/{r2.confidence.d}")
    print(f"    spread:    {r2.entropy.n}/{r2.entropy.d}")
    print(f"    z_conf:    {r2.z_conf}/{RESOLUTION}")
    print(f"    z_entr:    {r2.z_entr}/{RESOLUTION}")
    print(f"    reason:    {r2.reason}")
    print()

    # ── Test: budget exhaustion ──
    r3 = void_out(spiked, 3, ostats)
    print("  EXHAUSTED (budget=3):")
    print(f"    decision:  {r3.decision}")
    print(f"    reason:    {r3.reason}")
    print()

    print("=== Zero numpy. Zero softmax. Zero log. Zero exp. ===")
    print("=== Every tick costs. Confidence is gap. Entropy is spread. ===")
