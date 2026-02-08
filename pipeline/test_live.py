"""
test_live.py - Live VOID Pipeline test with Phi-3

Builds population stats from calibration prompts, then tests
the pipeline with population-relative confidence gating.
"""

import torch
from transformers import AutoModelForCausalLM, AutoTokenizer
from void_pipeline import void_pipeline, build_population_stats

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
print(f"  Embedding mean shape: {population_stats['mean'].shape}")
print(f"  Confidence: mean={output_stats['confidence']['mean']:.4f}, std={output_stats['confidence']['std']:.4f}")
print(f"  Entropy:    mean={output_stats['entropy']['mean']:.4f}, std={output_stats['entropy']['std']:.4f}")
print("Stats ready.\n")

# ═══════════════════════════════════════════════════════
# 3. TEST PROMPTS
# ═══════════════════════════════════════════════════════
test_cases = [
    # factual - should be confident
    ("What is 2+2?", 50000),
    ("The capital of France is", 50000),
    ("Water boils at", 50000),

    # abstract - less confident
    ("What is consciousness?", 50000),
    ("What is love?", 50000),
    ("What is the meaning of life?", 50000),

    # gibberish - should be dont_know
    ("asdf jkl qwerty", 50000),
    ("xyzzy plugh abracadabra", 50000),

    # budget starvation
    ("What is 2+2?", 500),
    ("What is 2+2?", 5),
]

print("=== VOID Pipeline Tests (z_threshold=1.0) ===\n")
for text, budget in test_cases:
    result = void_pipeline(
        text=text,
        budget=budget,
        model=model,
        tokenizer=tokenizer,
        population_stats=population_stats,
        output_stats=output_stats,
        z_threshold=1.0,
    )

    print(f'Prompt: "{text}"')
    print(f"  Budget:     {budget}")
    print(f"  Decision:   {result.decision}")
    print(f"  Response:   {result.response}")
    print(f"  Heat:       {result.total_heat}")
    print(f"  Remaining:  {result.budget_remaining}")

    if result.void_out_result:
        vo = result.void_out_result
        print(f"  Confidence: {vo.confidence} (z={vo.z_conf:.2f})")
        print(f"  Entropy:    {vo.entropy} (z={vo.z_entr:.2f})")
        print(f"  Reason:     {vo.reason}")

    print()

# ═══════════════════════════════════════════════════════
# 4. THRESHOLD SWEEP (find sweet spot)
# ═══════════════════════════════════════════════════════
print("=== Threshold Sweep on 'What is 2+2?' ===\n")
for zt in [0.0, 0.5, 1.0, 1.5, 2.0]:
    r = void_pipeline(
        "What is 2+2?", 50000, model, tokenizer,
        population_stats, output_stats, z_threshold=zt,
    )
    vo = r.void_out_result
    print(f"  z_threshold={zt:.1f}  decision={r.decision:<10}  "
          f"z_conf={vo.z_conf:.2f}  z_entr={vo.z_entr:.2f}  "
          f"response={r.response}")