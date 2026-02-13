"""
void_mid_layer.py - VOID-MID Layer (Parasitic Inter-Layer Gate)

Pure VOID logic. No numpy. No torch. No floats.
Ratio(n, d) and integer arithmetic only.

This file receives ALREADY QUANTIZED hidden states (list of Ratio).
The transduction boundary (float→Ratio) lives in void_hooked_model.py.

Classical early exit: "the answer is good enough, skip remaining layers"
VOID early exit:     "I lack budget or confidence — I REFUSE to continue"

Every operation costs one tick of heat. You cannot think for free.
"""

from typing import NamedTuple, List, Optional


class Ratio(NamedTuple):
    n: int
    d: int


class VoidMidResult(NamedTuple):
    should_continue: bool
    layer_index: int
    confidence_n: int          # numerator, denominator = RESOLUTION
    divergence_n: int          # numerator, denominator = RESOLUTION
    heat: int
    budget_remaining: int
    reason: str


# ── constants ──
RESOLUTION = 1000
COST_COMPARE = 1       # per dimension: compare to population
SAMPLE_DIMS = 64       # we sample, not scan all 3072 — budget!


# ── Ratio arithmetic (integer only) ──

def ratio_sub(a: Ratio, b: Ratio) -> Ratio:
    """a - b. Cross multiply. Integer."""
    return Ratio(a.n * b.d - b.n * a.d, a.d * b.d)


def ratio_abs(r: Ratio) -> Ratio:
    """Absolute value. Integer."""
    return Ratio(abs(r.n), r.d)


def ratio_gt(a: Ratio, b: Ratio) -> bool:
    """a > b? Cross multiply. Integer."""
    return a.n * b.d > b.n * a.d


def ratio_div_int(r: Ratio, k: int) -> Ratio:
    """r / k. Multiply denominator. Integer."""
    return Ratio(r.n, r.d * k)


# ── Population statistics (all Ratio) ──

class VoidMidPopulation:
    """
    Population statistics for hidden states at one layer position.
    Stored as Ratio. Computed from Ratio. No floats ever.
    """
    def __init__(self):
        self.mean: List[Ratio] = []
        self.spread: List[Ratio] = []   # mean absolute deviation
        self.n_samples: int = 0
        self.dims: int = 0

    def build_from_samples(self, samples: List[List[Ratio]]):
        """
        Build population from already-quantized hidden states.
        Mean and MAD computed in integer arithmetic.
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


# ── The Gate ──

class VoidMidGate:
    """
    Parasitic gate between transformer layers.
    Receives quantized hidden states. Decides: continue or exit.
    Pure integer logic.
    """

    def __init__(
        self,
        layer_positions: List[int] = None,
        z_threshold_n: int = -1000,   # confidence threshold (n/RESOLUTION)
        budget: int = 100000,
    ):
        self.layer_positions = layer_positions or [8, 16, 24]
        self.z_threshold_n = z_threshold_n
        self.initial_budget = budget
        self.budget = budget
        self.total_heat = 0
        self.results: List[VoidMidResult] = []

        # Population per layer
        self.populations: dict = {}  # layer_idx → VoidMidPopulation

        # Exit state
        self.should_exit = False
        self.exit_reason = ""
        self.exit_layer = -1

    def reset(self, budget: Optional[int] = None):
        """Reset for new inference pass."""
        self.budget = budget if budget is not None else self.initial_budget
        self.total_heat = 0
        self.results = []
        self.should_exit = False
        self.exit_reason = ""
        self.exit_layer = -1

    def evaluate(
        self,
        quantized_state: List[Ratio],
        layer_index: int,
    ) -> VoidMidResult:
        """
        Gate a hidden state that has ALREADY been quantized to Ratio.

        Args:
            quantized_state: list of Ratio — the hidden state after transduction
            layer_index: which transformer layer this came from

        Returns:
            VoidMidResult — continue or exit
        """
        dims = len(quantized_state)

        # How many dims we'll sample
        n_sample = min(SAMPLE_DIMS, dims)
        cost = n_sample * COST_COMPARE

        # ── Budget check ──
        if self.budget < cost:
            result = VoidMidResult(
                should_continue=False,
                layer_index=layer_index,
                confidence_n=0,
                divergence_n=0,
                heat=0,
                budget_remaining=self.budget,
                reason="budget exhausted at mid-layer",
            )
            self.should_exit = True
            self.exit_reason = result.reason
            self.exit_layer = layer_index
            self.results.append(result)
            return result

        # ── No population → pass through ──
        if layer_index not in self.populations:
            self.budget -= cost
            self.total_heat += cost
            result = VoidMidResult(
                should_continue=True,
                layer_index=layer_index,
                confidence_n=0,
                divergence_n=0,
                heat=cost,
                budget_remaining=self.budget,
                reason="no population data — pass through",
            )
            self.results.append(result)
            return result

        pop = self.populations[layer_index]

        # ── Sample dimensions evenly ──
        step = max(1, dims // n_sample)
        indices = list(range(0, dims, step))[:n_sample]

        # ── Per-dimension deviation (integer arithmetic) ──
        heat = 0
        total_z_n = 0   # accumulated z-score numerators

        for idx in indices:
            if idx >= pop.dims:
                heat += COST_COMPARE
                continue

            # deviation = |state[idx] - mean[idx]| / spread[idx]
            # All Ratio with d=RESOLUTION, so we work with numerators:
            dev_n = abs(quantized_state[idx].n - pop.mean[idx].n)
            spread_n = pop.spread[idx].n  # guaranteed >= 1

            # z for this dim = dev_n / spread_n (integer division, scale by RESOLUTION)
            z_dim_n = (dev_n * RESOLUTION) // spread_n

            total_z_n += z_dim_n
            heat += COST_COMPARE

        self.budget -= heat
        self.total_heat += heat

        # ── Average divergence ──
        n_checked = len(indices)
        avg_divergence_n = total_z_n // n_checked if n_checked > 0 else 0

        # ── Confidence = 2*RESOLUTION - divergence ──
        # Population norm divergence ≈ RESOLUTION (1.0 in z-score)
        # If divergence > 2*RESOLUTION (2.0 z-scores) → confidence negative → exit
        confidence_n = 2 * RESOLUTION - avg_divergence_n

        # ── Decision: integer comparison ──
        should_continue = confidence_n > self.z_threshold_n

        if should_continue:
            reason = (
                f"continue: conf={confidence_n}/{RESOLUTION} "
                f"div={avg_divergence_n}/{RESOLUTION} layer={layer_index}"
            )
        else:
            reason = (
                f"EARLY EXIT: conf={confidence_n}/{RESOLUTION} "
                f"div={avg_divergence_n}/{RESOLUTION} layer={layer_index}"
            )
            self.should_exit = True
            self.exit_reason = reason
            self.exit_layer = layer_index

        result = VoidMidResult(
            should_continue=should_continue,
            layer_index=layer_index,
            confidence_n=confidence_n,
            divergence_n=avg_divergence_n,
            heat=heat,
            budget_remaining=self.budget,
            reason=reason,
        )
        self.results.append(result)
        return result


# ─────────────────────────────────────────────
if __name__ == "__main__":
    print("=== VOID-MID: Pure Integer Test ===")
    print()

    # Ratio arithmetic
    a = Ratio(750, 1000)
    b = Ratio(500, 1000)
    diff = ratio_sub(a, b)
    print(f"  {a.n}/{a.d} - {b.n}/{b.d} = {diff.n}/{diff.d}")

    # Population from quantized samples
    pop = VoidMidPopulation()
    samples = [
        [Ratio(100, 1000), Ratio(200, 1000), Ratio(300, 1000), Ratio(400, 1000)],
        [Ratio(110, 1000), Ratio(190, 1000), Ratio(310, 1000), Ratio(410, 1000)],
        [Ratio(90, 1000),  Ratio(210, 1000), Ratio(290, 1000), Ratio(390, 1000)],
        [Ratio(105, 1000), Ratio(195, 1000), Ratio(305, 1000), Ratio(405, 1000)],
        [Ratio(95, 1000),  Ratio(205, 1000), Ratio(295, 1000), Ratio(395, 1000)],
    ]
    pop.build_from_samples(samples)
    print(f"  Pop: {pop.n_samples} samples, {pop.dims} dims")
    print(f"  Mean[0]={pop.mean[0].n}/{pop.mean[0].d}  "
          f"Spread[0]={pop.spread[0].n}/{pop.spread[0].d}")
    print()

    # Gate: normal state
    gate = VoidMidGate(layer_positions=[8], budget=10000)
    gate.populations[8] = pop

    normal = [Ratio(100, 1000), Ratio(200, 1000), Ratio(300, 1000), Ratio(400, 1000)]
    r1 = gate.evaluate(normal, layer_index=8)
    print(f"  Normal:    continue={r1.should_continue}  {r1.reason}")

    # Gate: divergent state
    gate.reset(10000)
    gate.populations[8] = pop
    divergent = [Ratio(900, 1000), Ratio(-500, 1000), Ratio(900, 1000), Ratio(-500, 1000)]
    r2 = gate.evaluate(divergent, layer_index=8)
    print(f"  Divergent: continue={r2.should_continue}  {r2.reason}")

    # Gate: budget exhaustion
    gate.reset(2)
    gate.populations[8] = pop
    r3 = gate.evaluate(normal, layer_index=8)
    print(f"  Exhausted: continue={r3.should_continue}  {r3.reason}")

    print()
    print("=== Zero floats. Zero imports. Every tick costs. ===")
