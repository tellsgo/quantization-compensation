# When Does Compensating Inherited Quantization Error Help?

**Mean-Square Guarantees for Layer-Wise Quantization and Their Limits**  
Tianhao Guo · College of Physics and Electronic Engineering, Shanxi University  
[tianhao_guo@sxu.edu.cn](mailto:tianhao_guo@sxu.edu.cn) · [ORCID](https://orcid.org/0000-0002-1317-868X)

Reproducibility code, saved measurements, three rigorous finite-support certificates, and a scoped Lean 4 source artifact for the paper.

## Quick start

Python 3.10 or newer:

```sh
python -m pip install numpy
python scripts/validate_reproduction.py
python scripts/validate_llm8b.py
```

This regenerates both plot sources and the gain table byte for byte, recomputes all 28 paired-teacher gain uncertainties, checks the trained-model table against saved per-layer measurements, and **replays the three fixed witnesses with rational arithmetic**. It also checks the distributed Lean file hashes. It does not run new model inference, Monte Carlo studies, or a Lean compiler.

The second command independently recomputes the Qwen3-8B and Meta-Llama-3-8B experiment numbers from the saved records, including the 84 policy/domain measurements, selection-size controls, suffix interventions and 48 two-bit slices. It needs only Python’s standard library. See the [8B reproduction guide](experiments/llm8b/README.md) for protocols and GPU reruns.

The 8B validation also checks the later [reuse/fresh selection experiment](experiments/llm8b/20261012_reuse_fresh/README.md): 20 paths and 2,176 adaptive decisions, with all candidate/window observations. Fresh windows did not halve network optimism or improve mean source-audit NLL in either model. This follow-up is separate from the original manuscript experiments. To recompute only this follow-up, run `python scripts/validate_reuse_fresh.py`; it uses only the standard library.

Generated figure sources appear in `reproduced_figures/`. They use pgfplots and the paper's macros and labels; include them in the manuscript to render them.

## Contents and scope

| Directory | What it provides |
|---|---|
| `numerics/` | Self-contained figure reproduction, original Python/NumPy simulation implementations, final saved results |
| `numerics/saved_witnesses/` | Three frozen inputs, exact rational risk/interval certificates, deterministic replay |
| `diagnostics/` | Saved per-layer measurements and portable layer-diagnostic runner; model/data assets must be acquired separately |
| `experiments/llm8b/` | Frozen 8B runners, configurations, raw numeric records, data/checkpoint fingerprints and offline checks |
| `lean/` | 110 Lean files, including 96 scientific modules; pinned dependencies, controls, scope map and historical build receipt |
| `docs/REPRODUCIBILITY.md` | Commands, provenance and limits |

The Lean source artifact covers **969 named declarations including auxiliary lemmas**, not 969 separate scientific results. It does not formalize every theorem in the paper. Its original v6.4 manuscript binding and historical validation receipt are preserved; the later editorial closeout and added repaired-composite proof do not constitute new Lean verification. Read [`lean/SCOPE.html`](lean/SCOPE.html) and [`lean/README.md`](lean/README.md).

## Lean build

Install Elan and use the pinned toolchain and lockfile:

```sh
cd lean
lake exe cache get
lake build
python3 scripts/check.py
```

Dependencies and their caches are downloaded separately. The distributed source is about 585 KiB; the full source artifact is about 864 KiB. A complete Mathlib/Lean build occupies substantially more disk and memory than this source package.

## License

The original code in this repository is released under **Apache-2.0**. Model weights, datasets, Lean and Mathlib are separate third-party works with their own licenses. The manuscript is distributed separately through arXiv; this code license does not assign the manuscript a publication license.
