"""
void_in_layer.py - VOID-IN Layer (Sensory Transduction Boundary)

Converts Phi-3 float32 embeddings to VOID Ratio representation.
The external world must finitize itself before speaking to us.

Pure integer logic after quantization. No numpy in VOID decisions.
Follows void_mid_layer.py standard: Ratio(n, d), MAD, integer z-scores.

Features:
- Fixed denominator (RESOLUTION=1000) prevents denominator explosion
- Existence threshold: below-noise numerators don't exist
- Entropy weights via integer MAD deviation from population
- Budget exhaustion: perception CAN be interrupted (incomplete=True)
- Every decision costs heat, even "this doesn't exist"

Transduction boundary: float→Ratio happens ONCE at the edge.
After that, float is dead. Ratio is born.
"""

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


# ── constants ──
RESOLUTION = 1000
EXISTENCE_THRESHOLD_N = 10    # |n| < 10 out of 1000 → doesn't exist
COST_PER_DIM = 1              # quantize one dimension
COST_WEIGHT = 1               # compute one entropy weight
DIM = 3072                    # Phi-3 embedding dimension


class VoidInPopulation:
    """
    Population statistics for embeddings.
    Stored as Ratio. Computed from Ratio. No floats ever.
    Mirrors VoidMidPopulation from void_mid_layer.py.
    """
    def __init__(self):
        self.mean: List[Ratio] = []
        self.spread: List[Ratio] = []   # mean absolute deviation
        self.n_samples: int = 0
        self.dims: int = 0

    def build_from_samples(self, samples: List[List[Ratio]]):
        """
        Build population from already-quantized embeddings.
        Mean and MAD computed in integer arithmetic.
        All samples must have d=RESOLUTION.
        """
        if not samples:
            return

        self.n_samples = len(samples)
        self.dims = len(samples[0])
        n = self.n_samples

        self.mean = []
        self.spread = []

        for dim_idx in range(self.dims):
            # Mean: sum of numerators / n (all have d=RESOLUTION)
            total_n = sum(s[dim_idx].n for s in samples)
            mean_n = total_n // n
            self.mean.append(Ratio(mean_n, RESOLUTION))

            # MAD: mean absolute deviation (no sqrt — no infinity)
            abs_dev_total = sum(abs(s[dim_idx].n - mean_n) for s in samples)
            mad_n = abs_dev_total // n
            mad_n = max(mad_n, 1)  # floor at 1 to prevent zero division
            self.spread.append(Ratio(mad_n, RESOLUTION))


def quantize_embedding(floats) -> List[Ratio]:
    """
    TRANSDUCTION BOUNDARY. Float dies here. Ratio is born.

    Accepts anything iterable of numbers (numpy array, list, etc).
    Returns list of Ratio with d=RESOLUTION.

    This is the ONE place where float→int conversion happens.
    After this function, no float exists in VOID.
    """
    result = []
    for f in floats:
        n = int(round(float(f) * RESOLUTION))
        result.append(Ratio(n, RESOLUTION))
    return result


def calculate_population_stats(embeddings_float) -> dict:
    """
    Build population statistics from float embeddings.

    TRANSDUCTION: quantizes all embeddings to Ratio FIRST,
    then computes stats in pure integer arithmetic.

    Args:
        embeddings_float: list of float arrays (from Phi-3)

    Returns:
        dict with 'population' (VoidInPopulation) and 'dim' (int)
    """
    # ── Transduction boundary: float → Ratio ──
    quantized_samples = []
    for emb in embeddings_float:
        quantized_samples.append(quantize_embedding(emb))

    # ── Pure integer statistics ──
    pop = VoidInPopulation()
    pop.build_from_samples(quantized_samples)

    return {
        'population': pop,
        'dim': pop.dims,
    }


def void_in(
    embedding_float,
    budget: int,
    population_stats: dict,
) -> VoidInResult:
    """
    Quantize float32 embedding to VOID Ratio with budget constraint.

    Args:
        embedding_float: shape (3072,), any numeric iterable (numpy ok at boundary)
        budget: max operations allowed
        population_stats: dict with 'population' (VoidInPopulation)

    Returns:
        VoidInResult — may be incomplete if budget exhausted

    TRANSDUCTION: float→Ratio happens once at entry.
    All decisions after that are pure integer.
    """
    pop = population_stats['population']
    dims = len(embedding_float) if hasattr(embedding_float, '__len__') else DIM

    result = [Ratio(0, RESOLUTION)] * dims
    weights = [Ratio(RESOLUTION, RESOLUTION)] * dims   # default weight = 1 = 1000/1000
    heat = 0
    cost_per_step = COST_PER_DIM + COST_WEIGHT

    processed = 0
    for i in range(dims):
        # a) budget check BEFORE any work
        if budget - heat < cost_per_step:
            return VoidInResult(
                embedding=result,
                weights=weights,
                heat=heat,
                budget_remaining=budget - heat,
                incomplete=True,
                processed_dims=processed,
            )

        # ── TRANSDUCTION: one float → one Ratio ──
        n = int(round(float(embedding_float[i]) * RESOLUTION))
        heat += COST_PER_DIM

        # b) existence threshold (integer comparison)
        if abs(n) < EXISTENCE_THRESHOLD_N:
            result[i] = Ratio(0, RESOLUTION)
            weights[i] = Ratio(0, RESOLUTION)   # zero weight: doesn't exist
            # existence check still costs
            processed += 1
            continue

        result[i] = Ratio(n, RESOLUTION)

        # c) entropy weight: how far from population mean?
        #    weight = RESOLUTION + z_n (so normal = 1000, unusual = 1000+)
        #    All integer. Mirrors void_mid_layer.py deviation logic.
        if i < pop.dims and pop.dims > 0:
            dev_n = abs(n - pop.mean[i].n)
            spread_n = pop.spread[i].n   # guaranteed >= 1
            # z for this dim: dev_n/spread_n scaled by RESOLUTION
            z_n = (dev_n * RESOLUTION) // spread_n
            # weight = 1.0 + z (in RESOLUTION units) capped at 5*RESOLUTION
            w_n = RESOLUTION + min(z_n, 4 * RESOLUTION)
            weights[i] = Ratio(w_n, RESOLUTION)
        else:
            weights[i] = Ratio(RESOLUTION, RESOLUTION)  # default weight = 1

        heat += COST_WEIGHT
        processed += 1

    return VoidInResult(
        embedding=result,
        weights=weights,
        heat=heat,
        budget_remaining=budget - heat,
        incomplete=False,
        processed_dims=processed,
    )


# ─────────────────────────────────────────────────────────
if __name__ == "__main__":
    print("=== VOID-IN: Pure Integer Test ===")
    print()

    # Transduction test
    test_floats = [0.123, -0.456, 0.789, 0.001, -0.999, 0.005]
    quantized = quantize_embedding(test_floats)
    print("  Transduction boundary:")
    for f, r in zip(test_floats, quantized):
        exists = "EXISTS" if abs(r.n) >= EXISTENCE_THRESHOLD_N else "GHOST"
        print(f"    {f:+.3f} → {r.n}/{r.d}  [{exists}]")
    print()

    # Population from quantized samples
    print("  Building population (integer only):")
    samples = [
        [Ratio(123, 1000), Ratio(-456, 1000), Ratio(789, 1000), Ratio(50, 1000)],
        [Ratio(130, 1000), Ratio(-440, 1000), Ratio(800, 1000), Ratio(55, 1000)],
        [Ratio(115, 1000), Ratio(-470, 1000), Ratio(775, 1000), Ratio(45, 1000)],
        [Ratio(128, 1000), Ratio(-450, 1000), Ratio(792, 1000), Ratio(52, 1000)],
        [Ratio(118, 1000), Ratio(-460, 1000), Ratio(782, 1000), Ratio(48, 1000)],
    ]
    pop = VoidInPopulation()
    pop.build_from_samples(samples)
    print(f"    {pop.n_samples} samples, {pop.dims} dims")
    for d in range(pop.dims):
        print(f"    dim[{d}]: mean={pop.mean[d].n}/{pop.mean[d].d}  "
              f"spread={pop.spread[d].n}/{pop.spread[d].d}")
    print()

    # Full pipeline test (with fake float embedding)
    stats = {'population': pop, 'dim': 4}
    fake_embedding = [0.123, -0.456, 0.789, 0.050]

    # Normal budget
    r1 = void_in(fake_embedding, 100, stats)
    print(f"  Normal:     processed={r1.processed_dims}/{4}  "
          f"heat={r1.heat}  incomplete={r1.incomplete}")
    for i in range(r1.processed_dims):
        print(f"    [{i}] {r1.embedding[i].n}/{r1.embedding[i].d}  "
              f"weight={r1.weights[i].n}/{r1.weights[i].d}")
    print()

    # Starved budget
    r2 = void_in(fake_embedding, 1, stats)
    print(f"  Starved:    processed={r2.processed_dims}/{4}  "
          f"heat={r2.heat}  incomplete={r2.incomplete}")
    print()

    print("=== Zero floats in VOID logic. Transduction at the boundary. ===")
