# 8B quantization-compensation experiments

Frozen experiment code and numeric records for **Qwen3-8B** and **Meta-Llama-3-8B**.
These experiments ask whether a correction chosen on calibration or selection
inputs remains useful on other inputs. They are RTN-backed QEP-style
implementations, not reproductions of the official QEP, QuIP, GPTQ or WaterSIC
pipelines.

## Recompute the reported numbers

From the repository root, with Python 3.10 or newer:

```sh
python scripts/validate_llm8b.py
```

This command needs **no GPU, model, text corpus or third-party Python package**.
It verifies the distributed archive, recomputes NLL/PPL from per-sequence losses,
rebuilds the 24 cells of the manuscript's 8B table and checks all reported win
counts. It also checks greedy choices, nested selection ranges, historical
native-forward receipts, suffix reversals and the two-bit coefficient results.
Reports and CSVs are written to `reproduced_llm8b/`.

This is a recalculation from stored observations. It does not regenerate model
outputs or rerun a GPU experiment. The repository's separate
`scripts/validate_reproduction.py` checks the earlier simulations, small-model
diagnostics, exact witnesses and Lean source hashes.

## What is included

| Directory | Scope | Recorded observations |
|---|---|---|
| `20261008_decision/` | 4-bit, seven policies, three calibration draws, two evaluation texts | Six runs; 84 policy/domain PPL measurements; 816 task-based choices |
| `20261008_selection_controls/` | 4-bit, nested selection sizes 4K/16K/32K, four policies | Twelve runs; four scored splits per policy; 1,632 task-based and 1,632 block-based choices |
| `20261008_suffix_interaction/` | Replay a fixed candidate under RTN and completed future blocks | Four runs; 48 nonterminal states and 16 terminal controls |
| `20261009_adaptive_strength/` | 2-bit, coefficient proposal and search-budget comparison | Four runs; 48 early/middle/late layer-group slices |
| `provenance/` | Source/result inventories, corpus hashes and checkpoint file hashes | No model weights or text corpus |

Each run includes its exact experiment-source snapshot, configuration in the
manifest, data fingerprints, completion receipt and raw numeric records. All
experiment Python files and numeric observation records are byte-identical to
the originals. Repeated source snapshots preserve the source/result binding.

Metadata paths are rewritten as public relative placeholders; decoded text
previews and private handoff prose are omitted. `provenance/FILES.json` records
both original and distributed hashes. Parent-manifest and protocol hashes retain
their original values in separate fields when sanitization changes their bytes.
The archive's path placeholders are provenance, not a ready-to-run installation.

## Protocol and interpretation

The quantizer uses asymmetric per-row groups of 128, bounded integer codes and
BF16 dequantized weights. Every candidate recomputes its scale and zero point.
Only decoder-block linear projections are quantized; embeddings, normalizations
and the language-model head stay at their original precision. Native Transformers
blocks provide RoPE, causal SDPA, residual connections and RMSNorm. This is not
packed low-bit inference, and the timings do not measure inference throughput.

The four groups, in dependency order, are q/k/v, attention output, gate/up and
down projection. Drift directions are fitted with ridge damping 1. An external
correction strength of 1 retains that ridge shrinkage; it is not an unregularized
full correction. The continuous quadratic in the two-bit campaign is a proposal
along this fitted direction. Its rank correlation with actual re-quantized
losses does not establish a smooth quantizer or a network-level guarantee.

All sequences have length 512; each sequence scores 511 next-token positions.
PPL is exponentiated mean sequence NLL. Table entries average PPL over draws,
not exponentiated pooled NLL. The evaluation sequences share a corpus and are
not statistically independent replicates. The 84 measurements are not 84
independent experiments.

- **Decision comparison:** fit on 2K tokens, select on 4K disjoint WikiText train
  tokens. Evaluate on the first 16,384 tokens of WikiText-2 **test** and the novel.
  `qep_half` uses external strength 0.5; `qep_no_down` also disables down-projection
  correction. Selectors consider strengths 0, 0.5 and 1. `local_select` uses linear
  reconstruction; `lookahead_select` includes the next RTN block; `task_select`
  scores a full RTN suffix; `directional_select` uses its gradient at the actual
  block output. Every policy follows its own quantized trajectory.
- **Selection controls:** retain the same 2K fit set and nest 4K/16K/32K selection
  sets. A separate 8K diagnostic set is excluded from choices. Evaluation uses
  tokens 65,536–81,919 of each evaluation text. `block_select` scores the current
  block and is distinct from the earlier one-block lookahead selector.
- **Suffix intervention:** preserve the current candidate and all earlier
  decisions, replacing only strictly later blocks by a fixed completed suffix.
  Eleven of 48 nonterminal states have a robust winner reversal at the fixed
  NLL margin 0.0001; none of those same pair/direction reversals recurs on the
  diagnostic set. This does not identify or exclude error cancellation.
- **Two-bit slices:** use unchanged RTN prefixes and discard each intervention
  after scoring. The analytic center beats fixed 0.5 on 47 of 48 diagnostic
  slices. Both theory-guided and fixed two-point searches also include a cached
  zero fallback. Fixed two-point search retains over 98% of the grid's aggregate
  diagnostic residual gain in all four model/draw conditions. The theory-guided
  search costs about 56% of grid search including common preparation, so the
  proposed 20% cost target fails. Its diagnostic advantage over the grid also
  fails. No complete-model two-bit PPL improvement or collapsed-model rescue is
  established. See the [full slice protocol](20261009_adaptive_strength/docs/specs/RUN_PROTOCOL.md).

Fixed half-strength beats RTN in all twelve model/draw/domain comparisons.
Task-based selection never increases its own stepwise selection objective, yet
loses to local selection in all six Llama draw/domain comparisons. The selection
control campaign directly compares those same two policies on selection and
held-out inputs; increasing selection size narrows the Llama evaluation gap but
does not eliminate it. No universal selector or causal failure mechanism follows.

## GPU reruns

The original environment was PyTorch `2.12.0.dev20260323+cu128`, Transformers
`5.3.0`, CUDA 12.8, on RTX PRO 6000 Blackwell Max-Q GPUs with 96 GB each. A run
uses one visible GPU; two GPUs allowed the models to run concurrently. The
programs hold multiple model/state copies. Smaller-memory configurations have
not been validated. Use a compatible CUDA PyTorch installation, plus:

```sh
python -m pip install 'transformers==5.3.0' 'numpy>=1.24,<3' safetensors pyarrow
```

The exact nightly PyTorch build may require an existing environment or a matching
wheel. Different framework builds or GPU architectures can change floating-point
results. Each new run records its environment. Native-forward checks should pass
before interpreting a changed environment's results.

Obtain the original [Qwen3-8B](https://huggingface.co/Qwen/Qwen3-8B) and
[Meta-Llama-3-8B](https://huggingface.co/meta-llama/Meta-Llama-3-8B) checkpoints
separately, subject to their access terms. These are not instruction-tuned Llama
weights. The runners use `local_files_only=True`; model directories must contain
the tokenizer as well as all weight shards. File fingerprints are in `provenance/`.

Prepare the public texts:

```sh
python experiments/llm8b/prepare_data.py --output experiments/llm8b/data
```

WikiText-2 raw train/test comes from a pinned
[Salesforce/wikitext revision](https://huggingface.co/datasets/Salesforce/wikitext/tree/b08601e04326c79dfdd32d625aee71d232d685c3).
Nonempty rows are joined with two newlines, retaining each row's whitespace.
The other text is Jane Austen's *Pride and Prejudice*,
[Project Gutenberg ebook 1342](https://www.gutenberg.org/ebooks/1342).
Only the Gutenberg wrapper is removed; front matter inside it is retained.
The helper requires the original transformed-text hashes and stops if an upstream
revision changes the text. Existing files with the recorded hashes can be used.

Verify inputs on CPU; replace the checkpoint path below with your own:

```sh
python experiments/llm8b/check_inputs.py --model-key qwen3 \
  --model /path/to/Qwen3-8B --data experiments/llm8b/data --weights
```

This hashes the checkpoint and reconstructs all archived token-array fingerprints
from the recorded offsets. Use `--model-key llama3` for Llama. The source texts
and token arrays are not redistributed here; their separate licenses and terms
continue to apply. No private core library is required.

Run one Qwen draw from the repository root:

```sh
CUDA_VISIBLE_DEVICES=0 python experiments/llm8b/run.py decision \
  --model /path/to/Qwen3-8B --data experiments/llm8b/data --draw 1 \
  --output experiments/llm8b/runs/qwen3_replicate_1

CUDA_VISIBLE_DEVICES=0 python experiments/llm8b/run.py selection \
  --model /path/to/Qwen3-8B --data experiments/llm8b/data --draw 1 \
  --selection-tokens 4096 --base experiments/llm8b/runs/qwen3_replicate_1 \
  --output experiments/llm8b/runs/qwen3_draw1_n4096

CUDA_VISIBLE_DEVICES=0 python experiments/llm8b/run.py suffix \
  --base experiments/llm8b/runs/qwen3_draw1_n4096 \
  --output experiments/llm8b/runs/qwen3_suffix_draw1

CUDA_VISIBLE_DEVICES=0 python experiments/llm8b/run.py adaptive \
  --base experiments/llm8b/runs/qwen3_draw1_n4096 \
  --output experiments/llm8b/runs/qwen3_adaptive_draw1
```

Outputs must be new directories. The launcher only resolves paths and selects
frozen configs; the archived numerical implementation is unchanged. Add
`--dry-run` to inspect an invocation without loading a model. For the complete
campaign, repeat decision draws 1–3 for each model; repeat selection draws 1–2 at
all three sizes; run suffix/adaptive on each model's two 4K selection parents.
Draw 3 belongs only to the decision campaign. Suffix and adaptive inherit their
draw from the supplied parent.

Fresh parent runs save token arrays, source snapshots and local model paths needed
by later stages. Do not pass the sanitized public archive directly as a parent.
Quantized checkpoint export is not implemented; schedules plus the original
checkpoint and inputs permit reconstruction.

## Implementation checks

These small CPU checks require PyTorch/Transformers but no downloaded model:

```sh
python experiments/llm8b/20261008_decision/tests/test_contract.py
python experiments/llm8b/20261008_decision/tests/test_suffix_gradient.py
```

They check bounded codes/dequantization, primal/dual ridge, zero drift, native
block parity, a suffix directional derivative and causal-prefix invariance.
The decision campaign's `scripts/verify_native.py --run PATH` checks native FP
and RTN forward passes on a fresh run. The selection campaign's
`scripts/replay_native.py --run PATH --policy task_select --output NEW.json`
rebuilds a recorded schedule and compares all four splits with native inference;
`block_select` is also supported. Historical receipts are included, and the
adaptive runner performs native parity checks before its slices.

Code is covered by the repository's **Apache-2.0** license. Model weights and
corpora remain separate third-party works. This code release does not modify the
manuscript or extend the Lean artifact's scope.
