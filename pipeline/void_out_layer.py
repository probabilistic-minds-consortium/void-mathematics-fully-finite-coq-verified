"""
void_out_layer.py - VOID-OUT Layer v2.0 (Decision Boundary)

Dynamic thresholds: "confident" means MORE confident than typical.
Not absolute certainty - relative certainty against population baseline.

A network that always says "dont_know" is honest but useless.
A network that always says "answer" is useful but dishonest.
Calibration against population finds the boundary.
"""

import numpy as np
from typing import List, NamedTuple
import math


class Ratio(NamedTuple):
    n: int
    d: int


class VoidOutResult(NamedTuple):
    decision: str              # "answer" | "dont_know" | "exhausted"
    top_token_id: int          # argmax token (-1 if no answer)
    confidence: Ratio          # top prob as Ratio
    entropy: Ratio             # distribution entropy as Ratio
    z_conf: float              # z-score of confidence vs population
    z_entr: float              # z-score of entropy vs population (inverted)
    logits_quantized: List[Ratio]
    heat: int
    budget_remaining: int
    reason: str


# --- constants ---
RESOLUTION = 1000
TOP_K = 32
COST_PER_LOGIT = 1
COST_CONFIDENCE = 1
COST_ENTROPY = 1
COST_SORT = 1
COST_SOFTMAX = 1


def _softmax(logits: np.ndarray) -> np.ndarray:
    """Numerically stable softmax."""
    x = logits - logits.max()
    e = np.exp(x)
    return e / e.sum()


def calculate_output_stats(logits_list: List[np.ndarray]) -> dict:
    """
    Precompute confidence and entropy stats from population of logits.
    Run on same prompts used for embedding stats.

    Returns:
        dict with 'confidence' and 'entropy' sub-dicts, each with mean/std
    """
    confidences = []
    entropies = []

    for logits in logits_list:
        probs = _softmax(logits)
        confidences.append(float(np.max(probs)))
        H = -float(np.sum(probs * np.log(probs + 1e-10)))
        entropies.append(H)

    conf_arr = np.array(confidences)
    entr_arr = np.array(entropies)

    return {
        'confidence': {
            'mean': float(conf_arr.mean()),
            'std': float(conf_arr.std() + 1e-8),
        },
        'entropy': {
            'mean': float(entr_arr.mean()),
            'std': float(entr_arr.std() + 1e-8),
        },
    }


def void_out(
    logits: np.ndarray,
    budget: int,
    output_stats: dict,
    z_threshold: float = 1.0,
) -> VoidOutResult:
    """
    Quantize top-k logits, compute confidence/entropy, decide via z-scores.

    Args:
        logits: shape (vocab_size,), dtype float32
        budget: remaining operations
        output_stats: from calculate_output_stats()
        z_threshold: how many stdevs above/below population to count as "sure"

    Returns:
        VoidOutResult with population-relative decision
    """
    heat = 0

    # minimum: sort + softmax + 2 logits + confidence + entropy
    min_cost = COST_SORT + COST_SOFTMAX + 2 * COST_PER_LOGIT + COST_CONFIDENCE + COST_ENTROPY
    if budget < min_cost:
        return VoidOutResult(
            decision="exhausted",
            top_token_id=-1,
            confidence=Ratio(0, 1),
            entropy=Ratio(0, 1),
            z_conf=0.0,
            z_entr=0.0,
            logits_quantized=[],
            heat=0,
            budget_remaining=budget,
            reason="budget exhausted before decision",
        )

    # 1) softmax over full vocab (needed for entropy)
    probs = _softmax(logits)
    heat += COST_SOFTMAX

    # 2) top-k indices
    top_k_indices = np.argpartition(logits, -TOP_K)[-TOP_K:]
    top_k_indices = top_k_indices[np.argsort(logits[top_k_indices])[::-1]]
    heat += COST_SORT

    # 3) quantize top-k
    quantized = []
    for idx in top_k_indices:
        if budget - heat < COST_CONFIDENCE + COST_ENTROPY:
            break
        val = float(logits[idx])
        n = int(round(val * RESOLUTION))
        quantized.append(Ratio(n, RESOLUTION))
        heat += COST_PER_LOGIT

    if len(quantized) < 2:
        return VoidOutResult(
            decision="exhausted",
            top_token_id=-1,
            confidence=Ratio(0, 1),
            entropy=Ratio(0, 1),
            z_conf=0.0,
            z_entr=0.0,
            logits_quantized=quantized,
            heat=heat,
            budget_remaining=budget - heat,
            reason="not enough budget for top-2",
        )

    # 4) confidence = max probability
    confidence_raw = float(np.max(probs))
    confidence = Ratio(int(round(confidence_raw * RESOLUTION)), RESOLUTION)
    heat += COST_CONFIDENCE

    # 5) entropy
    entropy_raw = -float(np.sum(probs * np.log(probs + 1e-10)))
    entropy = Ratio(int(round(entropy_raw * 100)), 100)
    heat += COST_ENTROPY

    # 6) z-scores against population
    pop_conf = output_stats['confidence']
    pop_entr = output_stats['entropy']

    z_conf = (confidence_raw - pop_conf['mean']) / pop_conf['std']
    z_entr = (pop_entr['mean'] - entropy_raw) / pop_entr['std']  # inverted: lower entropy = better

    # 7) decision
    if z_conf >= z_threshold and z_entr >= z_threshold:
        decision = "answer"
        top_token_id = int(top_k_indices[0])
        reason = f"z_conf={z_conf:.2f}, z_entr={z_entr:.2f}, threshold={z_threshold}"
    else:
        decision = "dont_know"
        top_token_id = -1
        parts = []
        if z_conf < z_threshold:
            parts.append(f"z_conf={z_conf:.2f} < {z_threshold}")
        if z_entr < z_threshold:
            parts.append(f"z_entr={z_entr:.2f} < {z_threshold}")
        reason = ", ".join(parts)

    return VoidOutResult(
        decision=decision,
        top_token_id=top_token_id,
        confidence=confidence,
        entropy=entropy,
        z_conf=z_conf,
        z_entr=z_entr,
        logits_quantized=quantized,
        heat=heat,
        budget_remaining=budget - heat,
        reason=reason,
    )


# ─────────────────────────────────────────────
if __name__ == "__main__":
    rng = np.random.default_rng(42)
    vocab = 32064

    # build fake population stats from 50 random logit vectors
    pop_logits = [rng.standard_normal(vocab).astype(np.float32) for _ in range(50)]
    ostats = calculate_output_stats(pop_logits)
    print(f"Population confidence: mean={ostats['confidence']['mean']:.4f}, std={ostats['confidence']['std']:.4f}")
    print(f"Population entropy:    mean={ostats['entropy']['mean']:.4f}, std={ostats['entropy']['std']:.4f}")

    # confident: spike at one token
    logits_spike = rng.standard_normal(vocab).astype(np.float32)
    logits_spike[1000] = 12.0
    out1 = void_out(logits_spike, 9999, ostats)
    print(f"\n=== SPIKED ===")
    print(f"decision: {out1.decision}")
    print(f"z_conf:   {out1.z_conf:.2f}")
    print(f"z_entr:   {out1.z_entr:.2f}")
    print(f"reason:   {out1.reason}")

    # flat
    logits_flat = rng.standard_normal(vocab).astype(np.float32) * 0.1
    out2 = void_out(logits_flat, 9999, ostats)
    print(f"\n=== FLAT ===")
    print(f"decision: {out2.decision}")
    print(f"z_conf:   {out2.z_conf:.2f}")
    print(f"z_entr:   {out2.z_entr:.2f}")
    print(f"reason:   {out2.reason}")