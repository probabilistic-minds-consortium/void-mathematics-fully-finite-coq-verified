"""
void_in_layer.py - VOID-IN Layer (Sensory Transduction Boundary)

Converts Phi-3 float32 embeddings to VOID Ratio representation.
The external world must finitize itself before speaking to us.

Features:
- Fixed denominator (RESOLUTION=1000) prevents denominator explosion
- Existence threshold: below-noise values don't exist
- Entropy weights: unusual dimensions get higher weight
- Budget exhaustion: perception CAN be interrupted (incomplete=True)
- Every decision costs heat, even "this doesn't exist"
"""

import numpy as np
from typing import List, NamedTuple


class Ratio(NamedTuple):
    n: int
    d: int


class VoidInResult(NamedTuple):
    embedding: List[Ratio]
    weights: List[Ratio]
    heat: int
    budget_remaining: int
    incomplete: bool
    processed_dims: int


# --- constants ---
RESOLUTION = 1000
EXISTENCE_THRESHOLD = 0.01
COST_PER_DIM = 1
COST_ENTROPY = 1
DIM = 3072


def calculate_population_stats(embeddings: List[np.ndarray]) -> dict:
    """
    Precompute mean/std per dimension from a corpus of embeddings.
    Run once on 1000+ samples, reuse forever.
    """
    stacked = np.stack(embeddings)
    return {
        'mean': stacked.mean(axis=0),
        'std': stacked.std(axis=0) + 1e-8,
    }


def void_in(
    embedding: np.ndarray,
    budget: int,
    population_stats: dict,
) -> VoidInResult:
    """
    Quantize float32 embedding to VOID Ratio with budget constraint.

    Args:
        embedding: shape (3072,), dtype float32
        budget: max operations allowed
        population_stats: dict with 'mean' and 'std' arrays (3072,)

    Returns:
        VoidInResult - may be incomplete if budget exhausted
    """
    mean = population_stats['mean']
    std = population_stats['std']

    result = [Ratio(0, 1)] * DIM
    weights = [Ratio(1, 1)] * DIM
    heat = 0
    cost_per_step = COST_PER_DIM + COST_ENTROPY

    processed = 0
    for i in range(DIM):
        # a) budget check
        if budget - heat < cost_per_step:
            return VoidInResult(
                embedding=result,
                weights=weights,
                heat=heat,
                budget_remaining=budget - heat,
                incomplete=True,
                processed_dims=processed,
            )

        f = float(embedding[i])

        # b) existence threshold
        if abs(f) < EXISTENCE_THRESHOLD:
            result[i] = Ratio(0, 1)
            weights[i] = Ratio(0, 1)
            heat += 1  # even "doesn't exist" costs
            processed += 1
            continue

        # c) quantize
        n = int(round(f * RESOLUTION))
        result[i] = Ratio(n, RESOLUTION)
        heat += COST_PER_DIM

        # d) entropy weight
        z = abs(f - float(mean[i])) / float(std[i])
        w_raw = 1.0 + z
        weights[i] = Ratio(int(round(w_raw * 100)), 100)
        heat += COST_ENTROPY

        processed += 1

    return VoidInResult(
        embedding=result,
        weights=weights,
        heat=heat,
        budget_remaining=budget - heat,
        incomplete=False,
        processed_dims=processed,
    )