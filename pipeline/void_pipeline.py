"""
void_pipeline.py - VOID Pipeline v2.0

Input → Tokenizer → Phi-3 Embedding → VOID-IN → Phi-3 Layers → VOID-OUT → Decision

Now with population-relative confidence gating.
"I don't know" means: I'm LESS sure than I usually am.
"""

import numpy as np
from typing import Optional, NamedTuple

try:
    import torch
    HAS_TORCH = True
except ImportError:
    HAS_TORCH = False

from void_in_layer import Ratio, VoidInResult, void_in, calculate_population_stats
from void_out_layer import VoidOutResult, void_out, calculate_output_stats


class VoidPipelineResult(NamedTuple):
    decision: str              # "answer" | "dont_know" | "exhausted"
    response: Optional[str]
    void_in_result: VoidInResult
    void_out_result: Optional[VoidOutResult]
    total_heat: int
    budget_remaining: int


COST_TOKENIZE = 1
COST_FORWARD = 1


def build_population_stats(prompts, model, tokenizer):
    """
    Build both embedding stats and output stats from a list of prompts.
    Run once, reuse forever.

    Returns:
        (population_stats, output_stats)
    """
    embeddings = []
    logits_list = []

    for prompt in prompts:
        inputs = tokenizer(prompt, return_tensors="pt")
        with torch.no_grad():
            outputs = model(**inputs, output_hidden_states=True)

        emb = outputs.hidden_states[1][0, -1, :].cpu().numpy()
        lgts = outputs.logits[0, -1, :].cpu().numpy()

        embeddings.append(emb)
        logits_list.append(lgts)

    population_stats = calculate_population_stats(embeddings)
    output_stats = calculate_output_stats(logits_list)

    return population_stats, output_stats


def void_pipeline(
    text: str,
    budget: int,
    model,
    tokenizer,
    population_stats: dict,
    output_stats: dict,
    z_threshold: float = 1.0,
) -> VoidPipelineResult:
    """
    Full VOID pipeline: text → decision with population-relative gating.
    """
    total_heat = 0

    # ── 1. BUDGET CHECK ──────────────────────────────
    if budget < COST_TOKENIZE + COST_FORWARD:
        empty_in = VoidInResult([], [], 0, budget, True, 0)
        return VoidPipelineResult("exhausted", None, empty_in, None, 0, budget)

    # ── 2. TOKENIZE ──────────────────────────────────
    inputs = tokenizer(text, return_tensors="pt")
    total_heat += COST_TOKENIZE
    budget -= COST_TOKENIZE

    # ── 3. PHI-3 FORWARD ─────────────────────────────
    with torch.no_grad():
        outputs = model(**inputs, output_hidden_states=True)
    total_heat += COST_FORWARD
    budget -= COST_FORWARD

    embedding = outputs.hidden_states[1][0, -1, :].cpu().numpy()
    logits = outputs.logits[0, -1, :].cpu().numpy()

    # ── 4. VOID-IN ────────────────────────────────────
    void_in_result = void_in(embedding, budget, population_stats)
    total_heat += void_in_result.heat
    budget -= void_in_result.heat

    if void_in_result.incomplete:
        return VoidPipelineResult(
            "exhausted", None, void_in_result, None, total_heat, budget
        )

    # ── 5. VOID-OUT ───────────────────────────────────
    void_out_result = void_out(logits, budget, output_stats, z_threshold)
    total_heat += void_out_result.heat
    budget -= void_out_result.heat

    # ── 6. DECISION ───────────────────────────────────
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
        void_out_result=void_out_result,
        total_heat=total_heat,
        budget_remaining=budget,
    )


# ═══════════════════════════════════════════════════════
# MOCK MODE
# ═══════════════════════════════════════════════════════

def void_pipeline_mock(
    text: str,
    budget: int,
    population_stats: dict,
    output_stats: dict,
    z_threshold: float = 1.0,
    embedding_dim: int = 3072,
    vocab_size: int = 32064,
    spike_token: int = -1,
) -> VoidPipelineResult:
    """
    Test pipeline with synthetic data. No model required.
    spike_token >= 0 injects high confidence at that token.
    """
    total_heat = 0

    if budget < COST_TOKENIZE + COST_FORWARD:
        empty_in = VoidInResult([], [], 0, budget, True, 0)
        return VoidPipelineResult("exhausted", None, empty_in, None, 0, budget)

    total_heat += COST_TOKENIZE + COST_FORWARD
    budget -= COST_TOKENIZE + COST_FORWARD

    seed = hash(text) % (2**31)
    rng = np.random.default_rng(seed)
    embedding = rng.standard_normal(embedding_dim).astype(np.float32)
    logits = rng.standard_normal(vocab_size).astype(np.float32)
    if spike_token >= 0:
        logits[spike_token] = 12.0

    void_in_result = void_in(embedding, budget, population_stats)
    total_heat += void_in_result.heat
    budget -= void_in_result.heat

    if void_in_result.incomplete:
        return VoidPipelineResult(
            "exhausted", None, void_in_result, None, total_heat, budget
        )

    void_out_result = void_out(logits, budget, output_stats, z_threshold)
    total_heat += void_out_result.heat
    budget -= void_out_result.heat

    if void_out_result.decision == "answer":
        response = f"[token_{void_out_result.top_token_id}]"
    else:
        response = None

    return VoidPipelineResult(
        decision=void_out_result.decision,
        response=response,
        void_in_result=void_in_result,
        void_out_result=void_out_result,
        total_heat=total_heat,
        budget_remaining=budget,
    )