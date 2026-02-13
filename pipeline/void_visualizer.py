"""
void_visualizer.py - VOID Terminal Visualizer

Real-time per-token confidence visualization in terminal.
ANSI colors, no external dependencies.

  green:  z_conf > 2*RESOLUTION  (very confident)
  yellow: z_conf 0 to 2*RESOLUTION  (moderate)
  red:    z_conf < 0  (uncertain)
  STOP:   generation halted

All z-scores are integer (n/RESOLUTION). No floats.

Usage:
    from void_visualizer import VoidVisualizer
    viz = VoidVisualizer()
    viz.display_trace(prompt, tokens, z_scores_n, decision)
"""


# ── ANSI escape codes ──
GREEN = "\033[92m"
YELLOW = "\033[93m"
RED = "\033[91m"
BOLD = "\033[1m"
DIM = "\033[2m"
RESET = "\033[0m"


def _z_color(z_n: int, resolution: int = 1000) -> str:
    """Pick color based on integer z-score (n/resolution)."""
    if z_n > 2 * resolution:
        return GREEN
    elif z_n > 0:
        return YELLOW
    else:
        return RED


def _z_dot(z_n: int, resolution: int = 1000) -> str:
    """Pick indicator based on integer z-score."""
    if z_n > 2 * resolution:
        return "[++]"
    elif z_n > 0:
        return "[+ ]"
    else:
        return "[--]"


class VoidVisualizer:
    """Terminal visualizer for VOID generation traces."""

    def __init__(self, resolution: int = 1000):
        self.resolution = resolution

    def display_trace(
        self,
        prompt: str,
        tokens: list,
        z_scores_n: list,
        stopped_reason: str,
        mid_layer_results: list = None,
    ):
        """
        Display a single prompt's generation trace.

        Args:
            prompt: input text
            tokens: list of generated token strings
            z_scores_n: list of integer z-score numerators (one per token)
            stopped_reason: why generation stopped
            mid_layer_results: optional list of VoidMidResult
        """
        r = self.resolution

        print(f'  {DIM}Prompt:{RESET} "{prompt}"')
        print()

        if not tokens:
            z = z_scores_n[0] if z_scores_n else 0
            print(f"    {RED}[REFUSED]{RESET} — zero tokens generated")
            print(f"    {DIM}z={z}/{r}{RESET}  {_z_dot(z, r)}")
        else:
            token_line = "    "
            z_line = "    "
            dot_line = "    "

            for i, tok in enumerate(tokens):
                z = z_scores_n[i] if i < len(z_scores_n) else 0
                color = _z_color(z, r)
                width = max(len(tok), 6)

                token_line += f"{color}{BOLD}{tok:<{width}}{RESET}  "
                z_line += f"{DIM}z={z}/{r}{RESET}" + " " * max(0, width - len(f"z={z}/{r}")) + "  "
                dot_line += f"{_z_dot(z, r)}" + " " * (width - 1) + "  "

            token_line += f"{DIM}[STOP]{RESET}"

            print(token_line)
            print(z_line)
            print(dot_line)

        # Stop reason
        reason_map = {
            "complete": "answer complete",
            "confidence_drop": "confidence below population norm",
            "budget": "budget exhausted",
            "max_tokens": "max tokens reached",
            "mid_layer_exit": "mid-layer early exit",
        }
        reason_text = reason_map.get(stopped_reason, stopped_reason)
        print(f"    {DIM}-> {reason_text}{RESET}")

        # Mid-layer results if present
        if mid_layer_results:
            print(f"    {DIM}mid-layers:{RESET}")
            for mr in mid_layer_results:
                cont = "OK" if mr.should_continue else "EXIT"
                print(f"      {DIM}L{mr.layer_index}: {cont} "
                      f"conf={mr.confidence_n}/{r} "
                      f"div={mr.divergence_n}/{r} "
                      f"heat={mr.heat}{RESET}")

        print()

    def display_header(self):
        """Print VOID header."""
        print()
        print(f"  {BOLD}{'=' * 55}{RESET}")
        print(f"  {BOLD} VOID: AI that knows when it doesn't know{RESET}")
        print(f"  {BOLD}{'=' * 55}{RESET}")
        print()

    def display_footer(self, total_heat: int = 0, budget_used: int = 0):
        """Print summary footer."""
        print(f"  {DIM}{'-' * 55}{RESET}")
        if total_heat > 0:
            print(f"  {DIM}total heat: {total_heat}  "
                  f"budget consumed: {budget_used}{RESET}")
        print(f"  {DIM}No fine-tuning. No retraining. No infinity.{RESET}")
        print(f"  {BOLD}{'=' * 55}{RESET}")
        print()

    def display_comparison(
        self,
        prompt: str,
        vanilla_output: str,
        vanilla_tokens: int,
        void_tokens: list,
        void_z_n: list,
        void_reason: str,
    ):
        """Side-by-side comparison: vanilla LLM vs VOID."""
        r = self.resolution

        print(f'  {DIM}Prompt:{RESET} "{prompt}"')
        print()
        print(f"    {DIM}Phi-3 vanilla:{RESET} \"{vanilla_output}\" ({vanilla_tokens} tokens)")

        if not void_tokens:
            z = void_z_n[0] if void_z_n else 0
            print(f"    {BOLD}Phi-3 + VOID:{RESET}  {RED}[REFUSED]{RESET} "
                  f"(0 tokens, z={z}/{r})")
        else:
            void_text = "".join(void_tokens)
            print(f"    {BOLD}Phi-3 + VOID:{RESET}  \"{void_text}\" "
                  f"({len(void_tokens)} tokens, {void_reason})")
        print()


# ─────────────────────────────────────────────────────────
if __name__ == "__main__":
    viz = VoidVisualizer()
    viz.display_header()

    # Simulate traces with integer z-scores
    viz.display_trace(
        prompt="The capital of France is",
        tokens=["Paris", "."],
        z_scores_n=[4730, 4330, 750],
        stopped_reason="confidence_drop",
    )

    viz.display_trace(
        prompt="2 + 2 =",
        tokens=["4"],
        z_scores_n=[5000, -1630],
        stopped_reason="confidence_drop",
    )

    viz.display_trace(
        prompt="Water boils at",
        tokens=["100", " degrees", " Celsius"],
        z_scores_n=[3330, 5690, 5830, -910],
        stopped_reason="confidence_drop",
    )

    viz.display_trace(
        prompt="What is the meaning of life?",
        tokens=[],
        z_scores_n=[-440],
        stopped_reason="confidence_drop",
    )

    viz.display_trace(
        prompt="asdf jkl qwerty",
        tokens=[],
        z_scores_n=[-2280],
        stopped_reason="confidence_drop",
    )

    viz.display_footer(total_heat=12450, budget_used=87550)
