# Reproduction and provenance

## What the quick check establishes

`python scripts/validate_reproduction.py` regenerates `fig_gain.tex`, `fig_relu.tex`, and `tab_split.tex` from the saved final measurements, requiring exact byte equality. It independently recomputes the 28 gain estimates and their standard errors from the 100 paired teacher clusters per setting. It verifies the four deterministic diagnostic columns, pooled weight-range percentages, and all three fixed witnesses. It verifies the complete distributed Lean hash list, but does not compile Lean.

The figure sources contain the manuscript's labels/macros; they are not standalone LaTeX documents. With the full manuscript source, compile from its root with `pdflatex main.tex` twice (TeX Live with pgfplots), or `tectonic main.tex` where available. The bibliography is embedded, so BibTeX is unnecessary.

## Synthetic experiments

The original implementations are retained in `numerics/`. Work in a separate scratch copy of that directory, because long-run scripts write their output JSON in the working directory:

```sh
python sim1_gain_depth.py
python sim2_gain_split.py
python sim3_relu.py
python crosscheck_numpy.py
```

The first three use the included pure-Python linear algebra. The cross-check uses NumPy and independent random streams. These are full Monte Carlo runs, not smoke tests. `results_sim1.json` and `results_sim3.json` are publication-facing summaries of the independent NumPy results; `sim2_gain_split.json` supplies the gain table. The committed summaries retain the corrected paired-teacher uncertainty. Rerunning a simulator alone does not update every publication-facing summary. The quick check uses the frozen final arrays and does not claim to rerun Monte Carlo. Seeds, sample sizes and estimator definitions are in the scripts and saved results.

## Three strict witnesses

`numerics/saved_witnesses/replay_fixed_witnesses.py --replay` enumerates the support of only the three supplied configurations. Inputs are interpreted as the exact binary floating-point values stored in JSON; arithmetic is rational. Commutator norms are enclosed by rational square-root intervals. It checks strict inequalities, all required Gram inversions, unchanged activation signs, and the first-layer convention.

The release evaluator retains the original function definitions byte for byte, with historical top-level path handling and execution removed. The wrapper's evaluator hash was updated accordingly. Input JSON and `SAVED_WITNESS_REPLAY.json` remain unchanged. There is no large-search completeness or constant-optimality claim.

## Trained-model diagnostic

The four compressed JSONL files in `diagnostics/data/` retain all 17,544 per-layer/mode/strength records. `range_energy.jsonl.gz` retains the separately measured range/energy data. Only machine-specific packet paths were made relative; numeric measurements were not changed. Packet hashes are provenance identities; activation arrays and packet binaries are not distributed.

`diagnostics/c6_core.py` is the original numerical implementation. `c6_run.py` retains the computation, model revisions, token offsets, thresholds, seeds and CPU settings. It replaces a private cache location with `HF_HUB_CACHE` (default `~/.cache/huggingface/hub`) and replaces the original internal review gate with a reproducible local source/input hash lock created by `prepare`. This is a release adaptation, not a claim that the archived run used this adapted wrapper.

To rerun from scratch, acquire the two public model snapshots listed in `diagnostics/ASSET_MANIFEST.json` and place these public source files under `diagnostics/public_sources/`:

- Project Gutenberg's *Pride and Prejudice* (ebook 1342), including its standard start/end wrapper, as `gutenberg_1342.txt`.
- WikiText-2 raw train and validation Parquet files, each with a `text` column, as `wikitext2_train.parquet` and `wikitext2_validation.parquet`.

The manifest records original asset hashes, package versions and token-array hashes. Verify them for historical comparability. Model/dataset redistribution and downloads follow their respective licenses. The repository contains no model weights or corpus text. The runner uses offline loading after assets are acquired. Install NumPy, PyTorch, Transformers, PyArrow, safetensors, huggingface_hub and psutil; the manifest records the historical versions rather than promising availability on every platform.

```sh
cd diagnostics
python c6_run.py prepare
python c6_run.py capture --model smol135 --dataset wikitext
python c6_run.py diagnose --model smol135 --dataset wikitext
```

Repeat capture/diagnose for both models and both texts. Captured activations can occupy substantial storage. Do not confuse this common-trajectory layer diagnostic with end-to-end compensated-model evaluation: it measures layer residuals, not perplexity or activation-stability hypotheses. `finite_core.py` supplies the original finite-codebook measurement kernel; `python range_measurements.py` reruns the range/energy measurements on the saved weights and corrections after all diagnostic cells have completed.

## Lean scope and historical validation

`lean/` is byte-identical to the accepted v6.4 public source artifact, including its scoped claim map, lockfiles, provenance and historical build receipt dated 2026-10-04. Its README's historical readiness comments describe that package's original stage. The manuscript's later editorial closeout and repaired composite proof are not a new formalization. No new Lean compile was performed for this release. The CI quick check verifies hashes only; use the Lean build commands in the root README for kernel checking.

The source package excludes Mathlib/Lean dependency caches, compiled project artifacts and private review conversations. Dependencies are fetched by the pinned build configuration and retain their own licenses.
