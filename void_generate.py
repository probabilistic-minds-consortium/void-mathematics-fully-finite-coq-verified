"""
void_generate.py - VOID Multi-Token Gating (System 2 Deliberation)

Generate token by token. Each step = separate VOID-OUT decision.
Generation can STOP mid-sentence when confidence drops or budget exhausts.

A honest half-sentence is worth more than a confident hallucination.
"""

import numpy as np
from typing import List, Optional, NamedTuple

try:
    import torch
    HAS_TORCH = True
except ImportError:
    HAS_TORCH = False

from void_in_layer import VoidInResult, void_in
from void_out_layer import VoidOutResult, void_out


class VoidGenerationResult(NamedTuple):
    tokens: List[int]
    text: str
    decisions: List[VoidOutResult]
    stopped_reason: str          # "complete" | "budget" | "confidence_drop" | "max_tokens"
    total_heat: int
    budget_remaining: int
    avg_z_conf: float
    min_z_conf: float
    void_in_result: VoidInResult


COST_FORWARD = 1


def void_generate(
    prompt: str,
    budget: int,
    model,
    tokenizer,
    population_stats: dict,
    output_stats: dict,
    max_tokens: int = 32,
    z_threshold: float = 1.0,
    confidence_floor: float = -1.0,
) -> VoidGenerationResult:
    """
    Multi-token generation with per-step VOID gating.

    Args:
        prompt: input text
        budget: total budget for ENTIRE generation
        model: Phi-3 model
        tokenizer: Phi-3 tokenizer
        population_stats: embedding stats (for VOID-IN)
        output_stats: logit stats (for VOID-OUT)
        max_tokens: generation limit
        z_threshold: passed to void_out per step
        confidence_floor: if z_conf drops below this → STOP
            set to -999.0 to never stop on confidence (diagnostic mode)

    Returns:
        VoidGenerationResult with per-token decisions
    """
    total_heat = 0
    generated_tokens = []
    decisions = []
    stopped_reason = "max_tokens"

    eos_id = tokenizer.eos_token_id

    # ── 1. TOKENIZE PROMPT ────────────────────────────
    input_ids = tokenizer(prompt, return_tensors="pt").input_ids

    # ── 2. VOID-IN on initial embedding ───────────────
    with torch.no_grad():
        init_out = model(input_ids, output_hidden_states=True)
    embedding = init_out.hidden_states[1][0, -1, :].cpu().numpy()
    total_heat += COST_FORWARD
    budget -= COST_FORWARD

    void_in_result = void_in(embedding, budget, population_stats)
    total_heat += void_in_result.heat
    budget -= void_in_result.heat

    if void_in_result.incomplete:
        return VoidGenerationResult(
            tokens=[],
            text="",
            decisions=[],
            stopped_reason="budget",
            total_heat=total_heat,
            budget_remaining=budget,
            avg_z_conf=0.0,
            min_z_conf=0.0,
            void_in_result=void_in_result,
        )

    # ── 3. GENERATION LOOP ────────────────────────────
    current_ids = input_ids

    for step in range(max_tokens):
        # a) forward pass
        if budget < COST_FORWARD + 36:  # forward + minimum void_out cost
            stopped_reason = "budget"
            break

        with torch.no_grad():
            outputs = model(current_ids)
        logits = outputs.logits[0, -1, :].cpu().numpy()
        total_heat += COST_FORWARD
        budget -= COST_FORWARD

        # b) VOID-OUT decision on this token
        decision = void_out(logits, budget, output_stats, z_threshold)
        total_heat += decision.heat
        budget -= decision.heat
        decisions.append(decision)

        # c) confidence check
        if decision.decision == "exhausted":
            stopped_reason = "budget"
            break

        if decision.decision == "dont_know" or decision.z_conf < confidence_floor:
            stopped_reason = "confidence_drop"
            break

        # d) accept token
        token_id = decision.top_token_id
        generated_tokens.append(token_id)

        # e) EOS check
        if token_id == eos_id:
            stopped_reason = "complete"
            break

        # f) extend sequence for next step
        new_token = torch.tensor([[token_id]], dtype=torch.long)
        current_ids = torch.cat([current_ids, new_token], dim=1)

    # ── 4. STATS ──────────────────────────────────────
    if decisions:
        z_confs = [d.z_conf for d in decisions]
        avg_z = sum(z_confs) / len(z_confs)
        min_z = min(z_confs)
    else:
        avg_z = 0.0
        min_z = 0.0

    text = tokenizer.decode(generated_tokens, skip_special_tokens=True)

    return VoidGenerationResult(
        tokens=generated_tokens,
        text=text,
        decisions=decisions,
        stopped_reason=stopped_reason,
        total_heat=total_heat,
        budget_remaining=budget,
        avg_z_conf=avg_z,
        min_z_conf=min_z,
        void_in_result=void_in_result,
    )


# ═══════════════════════════════════════════════════════
# LIVE TEST
# ═══════════════════════════════════════════════════════

if __name__ == "__main__" and HAS_TORCH:
    from transformers import AutoModelForCausalLM, AutoTokenizer
    from void_pipeline import build_population_stats

    print("=== Loading Phi-3 ===")
    model_name = "microsoft/Phi-3-mini-4k-instruct"
    tokenizer = AutoTokenizer.from_pretrained(model_name, trust_remote_code=True)
    model = AutoModelForCausalLM.from_pretrained(
        model_name, trust_remote_code=True, torch_dtype=torch.float32,
    )
    model.eval()
    print("Done.\n")

    calibration = [
        "What is love?", "How do I cook pasta?",
        "What is the capital of France?", "Explain quantum physics.",
        "Who was Einstein?", "What is 2+2?",
        "Tell me a joke.", "What is consciousness?",
        "How does gravity work?", "What is machine learning?",
        "How do birds fly?", "What is democracy?",
        "Explain photosynthesis.", "What is the speed of light?",
        "How do computers work?", "What is philosophy?",
    ]

    print("=== Building stats ===")
    pop_stats, out_stats = build_population_stats(calibration, model, tokenizer)
    print(f"  Confidence: mean={out_stats['confidence']['mean']:.4f}, std={out_stats['confidence']['std']:.4f}")
    print(f"  Entropy:    mean={out_stats['entropy']['mean']:.4f}, std={out_stats['entropy']['std']:.4f}")
    print()

    # ── Test cases ────────────────────────────────────

    test_prompts = [
        # completions (should generate confidently)
        ("The capital of France is", 100000, 1.0, -999.0, "completion, no floor"),
        ("2 + 2 =", 100000, 1.0, -999.0, "math completion, no floor"),
        ("Water boils at", 100000, 1.0, -999.0, "fact completion, no floor"),

        # completions with confidence floor
        ("The capital of France is", 100000, 1.0, 0.0, "completion, floor=0.0"),
        ("2 + 2 =", 100000, 1.0, 0.0, "math, floor=0.0"),

        # questions (harder)
        ("What is 2+2? The answer is", 100000, 1.0, -999.0, "guided question"),

        # gibberish
        ("asdf jkl qwerty", 100000, 1.0, -999.0, "gibberish, no floor"),

        # budget starvation
        ("The capital of France is", 7000, 1.0, -999.0, "starved budget"),
    ]

    for prompt, budget, zt, cf, label in test_prompts:
        r = void_generate(
            prompt, budget, model, tokenizer,
            pop_stats, out_stats,
            max_tokens=16, z_threshold=zt, confidence_floor=cf,
        )

        print(f'=== {label} ===')
        print(f'  Prompt:  "{prompt}"')
        print(f'  Output:  "{r.text}"')
        print(f'  Tokens:  {len(r.tokens)} generated')
        print(f'  Stopped: {r.stopped_reason}')
        print(f'  Heat:    {r.total_heat}')
        print(f'  Budget:  {r.budget_remaining} remaining')
        print(f'  z_conf:  avg={r.avg_z_conf:.2f}, min={r.min_z_conf:.2f}')

        if r.decisions:
            print(f'  Per-token z_conf: [{", ".join(f"{d.z_conf:.2f}" for d in r.decisions)}]')

        print()

elif __name__ == "__main__":
    print("[torch not available - need Phi-3 for live test]")
