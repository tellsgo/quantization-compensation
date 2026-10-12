# Reuse/fresh release checks — 2026-10-12

This update adds the completed follow-up experiment without modifying the
manuscript or the four previously published 8B campaigns. It preserves the
predeclared negative result: P2 and P3 fail in both models. The frozen threshold's
four correct source-audit decisions do not establish a universal selector.

Release validation completed:

- The original simulation/witness/Lean-hash suite and original four-campaign 8B
  suite pass. This is not a new Lean build.
- The new standard-library validator checks the original/public manifests,
  source/result binding, complete candidate/window records, selector actions,
  window separation, telescoping and historical native-forward receipts.
- It recomputes 20 paths and 2,176 adaptive decisions. The report, CSV, summary
  and recomputation receipt are byte-identical to the original experiment outputs.
- All numerical runners, observations, configurations and the analysis script
  retain their original bytes. Public metadata changes are itemized in the new
  campaign's `provenance/FILES.json`. The original freeze manifest is preserved.
- The released tiny-model test passes in the original PyTorch/Transformers
  environment, with CUDA disabled. It exercises all six path modes, candidate
  identity, native baseline reconstruction and fresh-window logging.
- The portable launcher's CPU-only preparation succeeds against the original
  checkpoints and public texts: all 22 checkpoint files match; regenerated token
  hashes, fitting tokens and both window plans match except for model locations.
- Source syntax, whitespace and public-path/secret scans pass. The repository
  checksum list covers the new distributed files as well as the earlier release.

No new complete 8B GPU campaign was run for packaging. The existing experimental
measurements, rather than rerun performance claims, are what this release makes
reproducible. Weights, datasets and a matching numerical environment are needed
for full inference replay; they are not needed for offline report recalculation.

GitHub Actions runs all three offline validation suites through the existing
validation entry points; `validate_llm8b.py` invokes the follow-up validator. Its
result is separate from these local checks. Original code remains Apache-2.0;
third-party weights/data and the manuscript have separate licenses.
