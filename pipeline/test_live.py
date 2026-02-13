"""
test_live.py - Live VOID Pipeline test with Phi-3

Builds population stats from calibration prompts, then tests
the pipeline with population-relative confidence gating.

All VOID z-scores are integer (n/RESOLUTION). No float thresholds.
"""

import torch
from transformers import AutoModelForCausalLM, AutoTokenizer
from void_pipeline import void_pipeline, build_population_stats
from void_out_layer import RESOLUTION

# ═══════════════════════════════════════════════════════
# 1. LOAD MODEL
# ═══════════════════════════════════════════════════════
print("=== Loading Phi-3 ===")
model_name = "microsoft/Phi-3-mini-4k-instruct"
tokenizer = AutoTokenizer.from_pretrained(model_name, trust_remote_code=True)
model = AutoModelForCausalLM.from_pretrained(
    model_name,
    trust_remote_code=True,
    torch_dtype=torch.float32,
)
model.eval()
print("Done.\n")

# ═══════════════════════════════════════════════════════
# 2. CALIBRATION PROMPTS (build population baseline)
# ═══════════════════════════════════════════════════════
calibration_prompts = [
    "What is love?",
    "What is hate?",
    "How do I cook pasta?",
    "What is the capital of France?",
    "Explain quantum physics.",
    "Who was Einstein?",
    "What is 2+2?",
    "Tell me a joke.",
    "What is consciousness?",
    "How does gravity work?",
    "What is the meaning of life?",
    "Describe a sunset.",
    "What is machine learning?",
    "How do birds fly?",
    "What is democracy?",
    "Explain photosynthesis.",
    "What is the speed of light?",
    "How do computers work?",
    "What is philosophy?",
    "Translate hello to Spanish.",
]

print("=== Building population stats ===")
population_stats, output_stats = build_population_stats(
    calibration_prompts, model, tokenizer
)
in_pop = population_stats['population']
out_pop = output_stats['population']
print(f"  IN:  {in_pop.n_samples} samples, {in_pop.dims} dims")
print(f"  OUT: gap_mean={out_pop.gap_mean_n}/{RESOLUTION}  "
      f"gap_MAD={out_pop.gap_mad_n}/{RESOLUTION}")
print(f"       spread_mean={out_pop.spread_mean_n}/{RESOLUTION}  "
      f"spread_MAD={out_pop.spread_mad_n}/{RESOLUTION}")
print("Stats ready.\n")

# ═══════════════════════════════════════════════════════
# 3. TEST PROMPTS
# ═══════════════════════════════════════════════════════
test_cases = [
    # factual — should be confident
    ("What is 2+2?", 500000),
    ("The capital of France is", 500000),
    ("Water boils at", 500000),

    # abstract — less confident
    ("What is consciousness?", 500000),
    ("What is love?", 500000),
    ("What is the meaning of life?", 500000),

    # gibberish — should be dont_know
    ("asdf jkl qwerty", 500000),
    ("xyzzy plugh abracadabra", 500000),

    # budget starvation
    ("What is 2+2?", 500),
    ("What is 2+2?", 5),
]

print("=== VOID Pipeline Tests (z_threshold=1000/1000) ===\n")
for text, budget in test_cases:
    result = void_pipeline(
        text=text,
        budget=budget,
        model=model,
        tokenizer=tokenizer,
        population_stats=population_stats,
        output_stats=output_stats,
        z_threshold_n=1000,  # 1.0 z-scores in integer
    )

    print(f'Prompt: "{text}"')
    print(f"  Budget:     {budget}")
    print(f"  Decision:   {result.decision}")
    print(f"  Response:   {result.response}")
    print(f"  Heat:       {result.total_heat}")
    print(f"  Remaining:  {result.budget_remaining}")

    if result.void_out_result:
        vo = result.void_out_result
        print(f"  Gap:        {vo.confidence.n}/{vo.confidence.d} (z={vo.z_conf}/{RESOLUTION})")
        print(f"  Spread:     {vo.entropy.n}/{vo.entropy.d} (z={vo.z_entr}/{RESOLUTION})")
        print(f"  Reason:     {vo.reason}")

    print()

# ═══════════════════════════════════════════════════════
# 4. THRESHOLD SWEEP (find sweet spot)
# ═══════════════════════════════════════════════════════
print("=== Threshold Sweep on 'What is 2+2?' ===\n")
for zt in [0, 500, 1000, 1500, 2000]:
    r = void_pipeline(
        "What is 2+2?", 500000, model, tokenizer,
        population_stats, output_stats, z_threshold_n=zt,
    )
    vo = r.void_out_result
    if vo:
        print(f"  z_threshold={zt}/{RESOLUTION}  decision={r.decision:<10}  "
              f"z_conf={vo.z_conf}/{RESOLUTION}  z_entr={vo.z_entr}/{RESOLUTION}  "
              f"response={r.response}")
    else:
        print(f"  z_threshold={zt}/{RESOLUTION}  decision={r.decision}")
