# Reusing versus refreshing selection windows

This follow-up experiment tests an explanation for the earlier 8B results:
does repeatedly choosing correction strengths on the same eight windows create
the network selector's optimism, and does using new windows at every decision
remove at least half of it?

**The frozen prediction failed in both models.** Refreshing the windows increased
the measured network optimism, and did not improve mean final source-audit NLL.
This withdraws the proposed explanation in these tested conditions; it does not
show that data reuse can never cause optimism or identify a replacement mechanism.

This is a later experiment, separate from the manuscript's original four
campaigns. It adds 20 path constructions, not 20 more entries to the earlier
84-measurement comparison. No manuscript revision is included in this release.

## Recompute without a GPU

From the repository root, with Python 3.10 or newer:

```sh
python scripts/validate_reuse_fresh.py
```

Only the Python standard library is needed. The command checks the archive and
window separation, recalculates choices and P1–P4 from saved per-window records,
and rebuilds the report in scratch space. It requires byte-identical agreement
with the archived report, JSON and CSV. Outputs go to
`reproduced_llm8b/reuse_fresh/`; the archive is not modified.

Read [FINAL_REPORT.md](results/FINAL_REPORT.md) for every draw and domain,
[all_metrics.csv](results/all_metrics.csv) for full precision, and the
[protocol](docs/specs/PROTOCOL.md) for the definitions and stopping rules.

| Mean over two selection draws | Network step optimism: reuse | Network step optimism: fresh | Fresh minus reuse source NLL |
|---|---:|---:|---:|
| Qwen3-8B | 0.03124441 | 0.07629877 | +0.00677715 |
| Meta-Llama-3-8B | 0.04146387 | 0.07641730 | +0.00105123 |

These optimism columns use the **same eight audit windows and the same summed
per-step definition** in both modes. The separate 32-window final-path statistic
is used for P1; substituting it on one side would change the comparison.

P1's positive network sign reproduced, but its complete numerical criterion
failed. P2 and P3 failed for both models. The frozen 0.035 threshold selected the
better policy on all four source-audit comparisons, while adopting one Llama draw
contrary to P4's predicted adoption pattern. This is not a universal threshold:
there are only two draws per model, and correctness is judged on the source audit,
not every domain. WikiText test and novel results remain separate in the report.

## What was fixed and what changed

The four fitting windows are the exact historical draw-1 fit set for each model,
shared across both new draws and every path. Both modes use eight selection
windows per decision; reuse repeats its first eight and fresh uses disjoint
groups. The candidate strengths are 0, 0.5 and 1. The quantizer, re-rounding,
ridge damping and native BF16 execution match the earlier selection controls.

Each model has eight adaptive paths (two draws, two modes, two selectors) and
RTN/half-strength baselines. The 16 adaptive paths contain 2,176 decisions. Every
decision retains three candidates' eight-window selection NLL, local MSE and
audit NLL vectors. The action is locked before the audit losses are computed.
The local selector reads MSE only. Final losses on all fresh selection windows
are retained in per-step groups, without a pooled selection loss.

Fresh uses 1,024 distinct windows for Llama and 1,152 for Qwen, versus eight for
reuse. It also recomputes prefixes. Thus the intervention changes unique text
coverage and runtime as well as reuse; it is not an equal-data-budget comparison.
There is one fixed fitting set per model, not independent replication over fits.

## Evidence and provenance

- `results/<model>/<path>/decisions.jsonl`: all candidate/window observations and actions.
- `results/<model>/<path>/results.json`: native final-forward losses on source, WikiText test and novel.
- `results/<model>/<fresh-path>/final_selection_windows.jsonl`: unpooled final-policy selection-window losses.
- `inputs/<model>/plan.json`: frozen window positions and text/token fingerprints.
- `verification/`: 48 same-prefix candidate checks are recorded in the per-path results; aggregate receipts here cover 12 baseline native-forward domain checks, checkpoint identity, timing and recomputation.
- `provenance/ORIGINAL_FREEZE.json`: original pre-run manifest, byte for byte.
- `provenance/FILES.json`: original/distributed file hashes and each release transformation.
- `docs/specs/FROZEN.json`: public snapshot, explicitly created after the experiment; it is not a new preregistration.

The numerical runners, analyzer, configurations, numeric observations and
candidate/native verification records are unchanged. The preparation script has
one interface change: the model directory is required instead of defaulting to
the original machine's path. Checkpoint paths and private document references
are sanitized; original plan/protocol hashes are retained. Original worker
manifests remain bound to the original freeze. Public plans have separate hashes.
Machine logs, private handoffs, model weights, text corpora and token arrays are
not redistributed.

The original run passed tiny-model implementation checks and all native baseline
checks; the maximum recorded baseline discrepancy is zero. Replaying receipts
does not rerun those GPU checks. Measured path time was 0.896 GPU-hours on one
available RTX PRO 6000; controller wall time was about 55 minutes. The path
timing includes audits and final fresh-window evaluation, and excludes loading.

## Rerun from the original inputs

Use the checkpoint acquisition, public text preparation and numerical environment
described in the [parent guide](../README.md#gpu-reruns). No private core is needed.
The checkpoint root must contain both `Qwen3-8B/` and `Meta-Llama-3-8B/`.

```sh
python experiments/llm8b/prepare_data.py --output experiments/llm8b/data

CUDA_VISIBLE_DEVICES=0 python experiments/llm8b/run_reuse_fresh.py \
  --models /path/to/checkpoints --data experiments/llm8b/data \
  --output experiments/llm8b/runs/reuse_fresh_replay
```

The launcher checks all checkpoint files and original text/token hashes,
recreates both window plans, and requires exact agreement except for the model
location. It snapshots replay inputs before inference, then runs both models
sequentially on the selected GPU and recomputes the report. Choose an available
GPU yourself; the launcher does not stop other processes. Outputs must be new
directories. The raw numerical implementation is unchanged.

Add `--prepare-only` to stop after CPU input verification, or `--dry-run` to
inspect the invocation without writing files or importing model libraries. After
`--prepare-only`, run `src/run.py --model-key qwen3`, then
`src/run.py --model-key llama3`, then `scripts/analyze.py` inside that new output
directory. Numerical agreement on a different PyTorch/CUDA stack is not assumed.

The small implementation check requires PyTorch and Transformers, but no weights:

```sh
python experiments/llm8b/20261012_reuse_fresh/tests/test_native.py
```

Original code is covered by the repository's Apache-2.0 license. Checkpoints and
datasets keep their own terms; the manuscript license is separate.
