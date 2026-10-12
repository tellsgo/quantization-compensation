> Public transcription: private navigation and handoff references were removed. Scientific settings, predictions and stopping rules are unchanged. The original protocol digest is retained in the original freeze manifest.

# Frozen protocol: reusing versus refreshing selection windows

Date: 2026-10-11 (Asia/Singapore). Directory name follows the task sheet's `20261012_reuse_fresh` contract. This protocol is frozen and hashed before any new 8B performance result. The pre-run task sheet's digest is retained in `../../provenance/ORIGINAL_FREEZE.json`. No manuscript, fork or public repository is modified.

## Question and scope

Test the predeclared hypothesis that repeatedly optimizing full-network NLL on the same eight windows induces the earlier network selection optimism, and that fresh windows substantially reduce it while changing local optimism little. This is a fixed-fit, new-selection experiment. It does not test a new quantizer or a universal generalization guarantee.

Two models: Qwen3-8B (36 blocks, 144 decisions) and Meta-Llama-3-8B (32 blocks, 128 decisions). Twenty path constructions: per model, two selection draws × reuse/fresh × task_select/local_select (eight paths), plus one RTN and one fixed half-strength path. The fitting set is the exact 2,048-token historical draw-1 fitting set, including its order, shared by all paths and both new draws for a model.

## Quantizer and numerical contract

Identical quantizer, ridge helper and native-block helper source bytes to the earlier selection-controls campaign: 4 bits, asymmetric groups of 128, integer codes 0–15, scales/zero points recomputed for every candidate, dequantized BF16 execution, damping 1, strengths 0/0.5/1. Decoder projection groups are q/k/v, attention output, gate/up, down. Embeddings, normalizations and output head remain BF16. Teacher and student use their own trajectories. There is no packed inference claim.

Each sequence is 512 tokens and contributes its mean NLL over 511 next-token predictions. All scalar selector scores are means of the saved per-window values. Local uses the sum of linear-map FP32 output MSEs, preserving the earlier objective; network uses native full-suffix NLL. This per-window aggregation can differ from a single global FP32 reduction by rounding; it is identical across both experimental arms and makes every decision independently reproducible from its log. Ties choose the smaller strength. TF32 is disabled; inference is deterministic given the numerical environment to the extent supplied by these kernels.

## Frozen sampling and capacity

New selection seeds are **2026101201** and **2026101202**. The common source audit seed is **2026101199**. None equals the historical 202610081–3. Plans and full token-array hashes are stored in `inputs/<model>/plan.json` and covered by the freeze manifest.

- The source audit consists of 32 uniformly sampled, aligned training windows excluding **all previously recorded training-role windows**, including the fitting set and both historical diagnostic sets. The first eight, in the sampled order, are the fixed per-step audit subset. They are excluded from every new selection path.
- The selection pool excludes F, the 32 source-audit windows and all 32 unique historical diagnostic windows. Other historical selection windows may occur in the new draw; the new selection draw itself is independently seeded. Across paths reuse is allowed.
- For each draw, sample a uniform permutation prefix without replacement of 8×T windows. Fresh uses consecutive groups of eight; reuse uses that same sequence's first eight at every step. Thus the modes share a starting sample and each fresh path has pairwise disjoint windows.
- Qwen: 4,916 complete training windows; 4,848 eligible selection windows; fresh requires 1,152.
- Llama: 4,755 complete training windows; 4,687 eligible selection windows; fresh requires 1,024.
- WikiText-2 test and novel both use token range **[32768,49152)**, 32 aligned windows. The historical metadata audit found no overlap with earlier evaluated ranges. Qwen text lengths: train 2,517,232 / test 298,938 / novel 171,750 tokens. Llama: 2,435,022 / 288,936 / 171,478. These texts are long enough.

The same three final audit sets are used for every path of a model and never select actions. Window separation is not independent-document sampling. Refreshing uses much more unique text and can require additional prefix recomputation: equal windows per decision and equal candidate counts do **not** mean equal unique data or total compute.

## Per-step logs and information boundary

For each of the 2,176 adaptive decisions, save all selection/audit starts, all three strengths' eight per-window full-network NLL values on selection, all three strengths' eight per-window local MSE values, all three strengths' eight per-window full-network NLL values on the fixed audit subset, the selector's scores, action, ridge and timings. There is **no reduced audit fallback** in this run.

Candidate generation accepts only original weights, F states and the fixed prefix. It does not accept selection or audit data. The action is chosen using `src/design.py:choose` **before** the audit losses are computed. Audit losses are appended only afterwards. Local records candidate NLLs, but its selector reads only MSE; network reads only NLL. No audit score is passed to either selector.

Future blocks stay RTN when a current action is evaluated. Already chosen groups in the current block and all earlier blocks stay fixed. Both modes use their own chosen prefixes. Fresh teacher/student prefixes are recomputed for that step's new windows; reuse and fixed-audit states are propagated without changing their inputs.

At path completion, run full native inference on the three final audit sets. Reuse also records its final policy on its eight selection windows. Fresh additionally records final-policy losses on every used selection window, grouped by the decision that used it, **without a pooled selection-set loss**. Those post-lock records are not fed back and do not enter P2/P4. Baselines record both new draws' eight reuse windows for matched path-level comparisons.

## Measures and predeclared decision rules

All gains use NLL, not local MSE. A step gain is the strength-zero candidate's mean NLL minus the chosen candidate's mean NLL, at the same current state and suffix. Step optimism is the selection gain minus the fixed-eight-audit gain. The path's step statistic sums these differences over all decisions.

For reuse, also report final-policy optimism relative to the same RTN baseline, separately on (a) the fixed eight audit windows and (b) all 32 source-audit windows. The step sum must agree with (a) up to the predeclared 1e-5 numerical tolerance; it need not equal (b). **P2 uses the step statistic in both arms.** Historical/P1 comparisons use the final-policy statistic against all 32 source-audit windows. This prevents an unequal-estimand comparison.

Primary summaries average the two new selection draws separately within each model. Every draw and every domain is still reported. Both models must pass for a joint prediction to pass. These are descriptive stopping rules, not significance tests or universal statements.

- **P1:** reuse network's mean path-level optimism lies in the literal predicted band 0.02–0.04; local's absolute mean optimism is at most 0.01. Also report the weaker condition “network optimism is positive” separately, so leaving the numerical band is not mislabeled a sign failure.
- **P2:** network reuse's mean step optimism must be positive, and fresh's must be at most half of it. Local fresh-minus-reuse mean step optimism must have absolute value at most 0.01. Both components must pass. If reuse is nonpositive, no positive-denominator reduction ratio is reported; the historical premise was not reproduced.
- **P3:** network fresh's mean final source-audit NLL is no greater than network reuse's. Report the paired per-draw differences as well; no noninferiority margin is added.
- **P4:** for each reuse draw, adopt network exactly when local-minus-network final selection NLL exceeds **0.035**; otherwise choose local. Prediction: reject both Llama draws, adopt both Qwen draws. Separately judge the decision on the source audit: the selected policy must have no larger NLL than the alternative (ties allowed). Report the selected policy's three domain NLLs. Neither the rule nor its threshold reads audit data.

## Stop and interpretation

Failure of P2 withdraws this operational reuse explanation for these tested settings; do not change seeds, thresholds, conditions or data windows in response. Candidate quality, objective mismatch and domain shift remain unproven alternative questions. Nonpositive network optimism in reuse is explicitly reported as historical non-reproduction, not proof that reuse is universally harmless. If P2 passes but P3 fails, report reduced measured optimism without a final-risk remedy. Novel is never pooled into an overall domain average. Do not add a 16K condition, rescue claim or new coefficient method.

## Validation before interpreting results

1. The complete logger/selector/reconstruction flow is exercised on a randomly initialized tiny Qwen model; this is an implementation test, not an 8B outcome.
2. Model input text/token hashes, historical F fingerprint, pool capacity, disjointness and unused evaluation ranges pass before inference.
3. At each adaptive path's first, middle and last decision, regenerate the candidates from the identical F and prefix and require exact tensor equality. Also compare first-step candidate hashes across both modes, policies and draws. The constructor's interface excludes selection data.
4. Check fixed-audit continuity between every pair of decisions and agreement with final native inference. Reuse selection-window continuity is checked as well.
5. RTN and half-strength get manual-prefix versus native-forward comparisons and fresh reconstructions from their recorded schedules on all three final domains, with maximum per-window NLL difference below 1e-6. This checks weight installation/state/masking; it is not an independent proof of ridge algebra.
6. `scripts/analyze.py` recomputes reported values and actions from per-window records and rejects missing, nonfinite or incomplete paths. No aggregate is manually copied into the report.

## Resources, timing and freeze

GPU 0 was initially occupied by another user's process (about 42.7 GB, high utilization); it is not interrupted. GPU 1 was idle. Start on an idle GPU only. The supervisor can use the other GPU if it becomes idle; otherwise it schedules the second model after the first finishes. No other user's process is killed.

The first predeclared path for each model is `task_select_reuse_draw1`. Measure that complete path, then record a cost-only budget receipt **before starting that model's next path** in `verification/budget_<model>.json`: the conservative remaining estimate is nine paths × 1.7 × measured first-path time. Across 20 paths the initial conservative envelope is 20 × 1.7 × the first measured path, with wall time depending on GPU availability. The task sheet's initial 5–15 hour estimate is a prior scheduling estimate, not a measured budget. Timing receipts are incorporated here by reference; they may revise the elapsed-time forecast but never the scientific protocol or hash. They read elapsed time only, not losses or decisions.

The first path's measurements are included, not discarded. Path order is fixed in `src/run.py:path_schedule`. No 8B outcomes are inspected for redesign. All runs record the frozen-manifest hash; source/config/plan hashes are checked on startup. After freeze, code changes require a documented implementation correction and new freeze version, with aborted evidence retained; there is no silent overwrite.

Deliver `results/FINAL_REPORT.md`, `results/summary.json`, `results/all_metrics.csv`, every path's raw records, `verification/` and this hashed protocol. The report ends with the implication for Section 9; the experiment did not edit the paper.
