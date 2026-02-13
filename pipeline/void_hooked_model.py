"""
void_hooked_model.py — Transduction Boundary

The WALL between the LLM world (float, PyTorch) and VOID (Ratio, integer).

Does three things:
  1. Registers PyTorch hooks on transformer layers
  2. Captures hidden states (float) at the boundary
  3. Quantizes to Ratio, passes to VoidMidGate (pure integer)

All VOID logic is in void_mid_layer.py. This file is plumbing.
Float touches Ratio ONCE at the quantize() call. After that, dead.
"""

try:
    import torch
    HAS_TORCH = True
except ImportError:
    HAS_TORCH = False

from typing import List
from void_mid_layer import Ratio, VoidMidGate, VoidMidPopulation, RESOLUTION


def quantize(floats) -> List[Ratio]:
    """
    TRANSDUCTION BOUNDARY. Float dies here. Ratio is born.
    Accepts list or any iterable of numbers.
    Returns list of Ratio with d=RESOLUTION.
    """
    out = []
    for f in floats:
        n = int(round(float(f) * RESOLUTION))
        out.append(Ratio(n, RESOLUTION))
    return out


def _get_layer(model, pos: int):
    """Get transformer layer by position. Tries common architectures."""
    try:
        return model.model.layers[pos]
    except (AttributeError, IndexError):
        pass
    try:
        return model.transformer.h[pos]
    except (AttributeError, IndexError):
        pass
    return None


class VoidHookedModel:
    """
    Wraps a model with VOID mid-layer gates via PyTorch hooks.
    The model is NEVER modified. Hooks observe, quantize, gate.
    """

    def __init__(self, model, tokenizer, gate: VoidMidGate):
        self.model = model
        self.tokenizer = tokenizer
        self.gate = gate
        self._hooks: list = []

    # ── Calibration ──

    def calibrate(self, prompts: List[str], device: str = "cpu"):
        """Build population statistics. Run once on diverse prompts."""
        captured = {}
        for pos in self.gate.layer_positions:
            captured[pos] = []
        hooks = []

        for pos in self.gate.layer_positions:
            layer = _get_layer(self.model, pos)
            if layer is None:
                continue

            def make_hook(p):
                def hook_fn(module, inp, output):
                    hs = output[0] if isinstance(output, tuple) else output
                    vals = hs[0, -1, :].detach().cpu().tolist()
                    # TRANSDUCTION: float → Ratio at the boundary
                    captured[p].append(quantize(vals))
                return hook_fn

            h = layer.register_forward_hook(make_hook(pos))
            hooks.append(h)

        with torch.no_grad():
            for prompt in prompts:
                inputs = self.tokenizer(prompt, return_tensors="pt").to(device)
                self.model(**inputs)

        for h in hooks:
            h.remove()

        for pos in self.gate.layer_positions:
            if captured[pos]:
                pop = VoidMidPopulation()
                pop.build_from_samples(captured[pos])
                self.gate.populations[pos] = pop

    # ── Inference hooks ──

    def install_hooks(self):
        """Install inference hooks. Call gate.reset() before each pass."""
        self._hooks = []

        for pos in self.gate.layer_positions:
            layer = _get_layer(self.model, pos)
            if layer is None:
                continue

            def make_hook(p):
                def hook_fn(module, inp, output):
                    if self.gate.should_exit:
                        return output
                    hs = output[0] if isinstance(output, tuple) else output
                    vals = hs[0, -1, :].detach().cpu().tolist()
                    # TRANSDUCTION: float → Ratio at the boundary
                    ratios = quantize(vals)
                    # Pure integer from here on
                    self.gate.evaluate(ratios, p)
                    return output
                return hook_fn

            h = layer.register_forward_hook(make_hook(pos))
            self._hooks.append(h)

    def remove_hooks(self):
        for h in self._hooks:
            h.remove()
        self._hooks = []

    @property
    def should_exit(self) -> bool:
        return self.gate.should_exit

    @property
    def exit_reason(self) -> str:
        return self.gate.exit_reason


if __name__ == "__main__":
    print("void_hooked_model.py — transduction boundary")
    print("Requires PyTorch model to run live.")
    print()
    print("Transduction test:")
    test = [123, -456, 789, 1, -999]
    for v in test:
        f = v / 1000
        r = quantize([f])[0]
        print("  %+.3f -> %d/%d" % (f, r.n, r.d))
