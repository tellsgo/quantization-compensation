# 8B release verification — 2026-10-10

The release preserves the original experiment implementations and numeric
observations. No new full 8B quantization campaign was run during packaging.

Completed checks:

- The earlier reproduction suite passed: figure-source reproduction, paired
  uncertainties, small-model diagnostic counts, three rational witness replays
  and Lean source hashes. No new Lean compilation is implied.
- The standalone 8B validator passed: 24 table cells, 12 table win counts,
  per-sequence NLL/PPL consistency, 816 decision-campaign task choices, 3,264
  selection-control choices, nested data ranges, suffix interventions, two-bit
  slices, historical native-forward receipts and analysis tests.
- All archived experiment Python sources and numeric observation records match
  their original SHA-256 hashes. Metadata sanitization is itemized in
  `experiments/llm8b/provenance/FILES.json`.
- Fresh public downloads reproduced the original hashes of WikiText-2 train,
  WikiText-2 test and the processed Gutenberg text.
- In the original PyTorch/Transformers environment, the released tiny-model
  tests passed: codebook/decode, primal/dual ridge, zero drift, native block
  parity, suffix directional derivative and causal-prefix invariance.
- Both complete checkpoint inventories, including all weight shards, matched.
  The input checker reconstructed all 62 recorded token-array fingerprints per
  model (124 total) from the public texts and each original tokenizer.
- All four experiment entry points loaded successfully in that environment;
  the portable launcher's decision invocation passed its path/config dry run.
- Python syntax checks and the release privacy/path scan passed.

GitHub Actions verifies the committed repository checksums and runs both offline
reproduction suites on each push. The action's result is separate from this
local release receipt. Full GPU reruns require externally acquired model weights,
texts and a compatible CUDA environment; no external private core is needed.
