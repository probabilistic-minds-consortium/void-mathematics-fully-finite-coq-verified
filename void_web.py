#!/usr/bin/env python3
"""
VOID-Web: Latent Space Spider Web
Step 1: Extract embeddings from Phi-3 Mini

Run: python3 void_web.py
"""

import torch
import numpy as np
from transformers import AutoModelForCausalLM, AutoTokenizer

print("="*60)
print("     VOID-Web: Building the Spider Web")
print("="*60)

# Load model
print("\n[1] Loading Phi-3 Mini...")
model_name = "microsoft/Phi-3-mini-4k-instruct"
tokenizer = AutoTokenizer.from_pretrained(model_name)
model = AutoModelForCausalLM.from_pretrained(model_name, trust_remote_code=True)
model.eval()
print("    Done!")

# Test prompts - different semantic regions
prompts = [
    "What is love?",
    "What is hate?",
    "What is mathematics?",
    "What is infinity?",
    "What is death?",
    "What is consciousness?",
    "What is fear?",
    "What is hope?",
    "How do I cook pasta?",
    "What is the capital of France?",
]

print(f"\n[2] Extracting embeddings from {len(prompts)} prompts...")

embeddings = []
for i, prompt in enumerate(prompts):
    inputs = tokenizer(prompt, return_tensors="pt")
    
    with torch.no_grad():
        outputs = model(**inputs, output_hidden_states=True)
    
    # Last hidden state, last token (most semantic info)
    last_hidden = outputs.hidden_states[-1]
    last_token_embedding = last_hidden[0, -1, :].numpy()
    
    embeddings.append({
        'prompt': prompt,
        'embedding': last_token_embedding,
        'dim': last_token_embedding.shape[0]
    })
    print(f"    [{i+1}/{len(prompts)}] {prompt[:30]}... dim={last_token_embedding.shape[0]}")

print(f"\n[3] Embedding dimension: {embeddings[0]['dim']}")

# Calculate similarities (cosine)
print("\n[4] Similarity matrix (cosine):")
print("-"*60)

def cosine_sim(a, b):
    return np.dot(a, b) / (np.linalg.norm(a) * np.linalg.norm(b))

# Print header
print(f"{'':>25}", end="")
for i in range(len(prompts)):
    print(f"{i:>6}", end="")
print()

for i, e1 in enumerate(embeddings):
    short_name = e1['prompt'][:22] + "..."
    print(f"{short_name:>25}", end="")
    for j, e2 in enumerate(embeddings):
        sim = cosine_sim(e1['embedding'], e2['embedding'])
        print(f"{sim:>6.2f}", end="")
    print()

# Find clusters
print("\n[5] Semantic clusters (similarity > 0.85):")
print("-"*60)
clusters = []
for i, e1 in enumerate(embeddings):
    for j, e2 in enumerate(embeddings):
        if i < j:
            sim = cosine_sim(e1['embedding'], e2['embedding'])
            if sim > 0.85:
                print(f"    {e1['prompt'][:25]:>25} <-> {e2['prompt'][:25]:<25} = {sim:.3f}")
                clusters.append((i, j, sim))

# Save for later
print("\n[6] Saving embeddings to void_embeddings.npz...")
np.savez('void_embeddings.npz',
    prompts=prompts,
    embeddings=np.array([e['embedding'] for e in embeddings])
)
print("    Done!")

print("\n" + "="*60)
print("     Next step: Build the spider web (clustering)")
print("="*60)
