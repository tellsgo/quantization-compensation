# Reuse versus fresh selection: final report

All 20 path constructions completed. All numbers below are recomputed from per-window records. No manuscript or public repository was changed.

## Frozen predictions

| Model | P1 numerical band | Network positive | P2 network halved | P2 local change <=0.01 | P2 joint | P3 source not worse | P4 predicted adoption |
|---|---|---|---|---|---|---|---|
| qwen3 | False | True | False | False | False | False | True |
| llama3 | False | True | False | True | False | False | False |

P1 uses final-policy optimism on the full 32-window source audit. Its predeclared band is network 0.02–0.04 and |local|<=0.01. P2 compares summed per-step NLL gain differences against the same fixed eight audit windows in both modes. Results are means of two selection draws with one fixed fit set; these are operational pass/fail rules, not significance tests.

## Optimism by policy, mode, model and draw

| Model | Policy | Mode | Draw | Summed step optimism (audit 8) | Final path optimism (audit 8) | Final path optimism (source 32) |
|---|---|---|---:|---:|---:|---:|
| qwen3 | local_select | fresh | 1 | -0.00484398 | — | — |
| qwen3 | local_select | fresh | 2 | +0.01374613 | — | — |
| qwen3 | local_select | reuse | 1 | +0.02379385 | +0.02379385 | +0.02212006 |
| qwen3 | local_select | reuse | 2 | +0.01285246 | +0.01285246 | +0.01231823 |
| qwen3 | task_select | fresh | 1 | +0.06963405 | — | — |
| qwen3 | task_select | fresh | 2 | +0.08296348 | — | — |
| qwen3 | task_select | reuse | 1 | +0.03175551 | +0.03175551 | +0.02929153 |
| qwen3 | task_select | reuse | 2 | +0.03073332 | +0.03073332 | +0.02899057 |
| llama3 | local_select | fresh | 1 | +0.02612898 | — | — |
| llama3 | local_select | fresh | 2 | -0.00957717 | — | — |
| llama3 | local_select | reuse | 1 | +0.00589760 | +0.00589760 | +0.00818157 |
| llama3 | local_select | reuse | 2 | +0.00730477 | +0.00730477 | +0.01523226 |
| llama3 | task_select | fresh | 1 | +0.08071458 | — | — |
| llama3 | task_select | fresh | 2 | +0.07212003 | — | — |
| llama3 | task_select | reuse | 1 | +0.04026781 | +0.04026781 | +0.03913450 |
| llama3 | task_select | reuse | 2 | +0.04265994 | +0.04265994 | +0.04926574 |

Fresh final-policy selection-window losses are stored individually in each path’s `final_selection_windows.jsonl`; they are not pooled into a selection-set score. Reuse step/path values agree for the SAME audit subset; changing audit 8 to source 32 changes the comparison sample.

## Final risk, domains kept separate

| Model | Policy | Mode | Draw | Source NLL | WikiText test NLL | Novel NLL | Total seconds |
|---|---|---|---:|---:|---:|---:|---:|
| qwen3 | local_select | fresh | 1 | 2.59843845 | 2.61048501 | 2.67199887 | 256.6 |
| qwen3 | local_select | fresh | 2 | 2.59306355 | 2.60587918 | 2.66182153 | 257.1 |
| qwen3 | local_select | reuse | 1 | 2.60075384 | 2.61269970 | 2.66528480 | 171.9 |
| qwen3 | local_select | reuse | 2 | 2.60180407 | 2.61291946 | 2.66643600 | 171.7 |
| qwen3 | qep_half | fixed | — | 2.61127659 | 2.62737963 | 2.66388013 | 21.5 |
| qwen3 | rtn | fixed | — | 2.62324264 | 2.64248811 | 2.67034570 | 13.4 |
| qwen3 | task_select | fresh | 1 | 2.58162172 | 2.59578365 | 2.64955756 | 257.0 |
| qwen3 | task_select | fresh | 2 | 2.56723571 | 2.59067168 | 2.63904252 | 257.0 |
| qwen3 | task_select | reuse | 1 | 2.57017417 | 2.58603189 | 2.63403258 | 167.7 |
| qwen3 | task_select | reuse | 2 | 2.56512895 | 2.58698462 | 2.65486738 | 171.7 |
| llama3 | local_select | fresh | 1 | 2.19537995 | 2.17256063 | 1.29019012 | 216.2 |
| llama3 | local_select | fresh | 2 | 2.19152782 | 2.17180876 | 1.27527061 | 216.2 |
| llama3 | local_select | reuse | 1 | 2.19332466 | 2.17246542 | 1.29124080 | 144.6 |
| llama3 | local_select | reuse | 2 | 2.19038506 | 2.17700400 | 1.30227606 | 145.6 |
| llama3 | qep_half | fixed | — | 2.18849834 | 2.17554839 | 1.31676217 | 20.5 |
| llama3 | rtn | fixed | — | 2.20734828 | 2.20429828 | 1.34952558 | 12.9 |
| llama3 | task_select | fresh | 1 | 2.19014187 | 2.18414689 | 1.32965893 | 216.2 |
| llama3 | task_select | fresh | 2 | 2.19669694 | 2.17759515 | 1.36445214 | 216.3 |
| llama3 | task_select | reuse | 1 | 2.19630404 | 2.18664108 | 1.35039569 | 144.9 |
| llama3 | task_select | reuse | 2 | 2.18843232 | 2.17422782 | 1.34533433 | 144.8 |

## Frozen-threshold rule (reuse only)

| Model | Draw | Selection gain vs local | Adopt network | Source gain vs local | Decision correct on source | Rule source NLL | Rule Wiki NLL | Rule novel NLL |
|---|---:|---:|---|---:|---|---:|---:|---:|
| qwen3 | 1 | +0.03775114 | True | +0.03057967 | True | 2.57017417 | 2.58603189 | 2.63403258 |
| qwen3 | 2 | +0.05334747 | True | +0.03667512 | True | 2.56512895 | 2.58698462 | 2.65486738 |
| llama3 | 1 | +0.02797355 | False | -0.00297938 | True | 2.19332466 | 2.17246542 | 1.29124080 |
| llama3 | 2 | +0.03598621 | True | +0.00195274 | True | 2.18843232 | 2.17422782 | 1.34533433 |

## Checks and cost

Validated 2176 adaptive decisions, all candidate/window matrices, 48 real-model same-prefix candidate checks, matched first-step candidates, fixed-audit telescoping and RTN/half native reconstructions on all three audit domains. Total measured path time: 0.896 GPU-hours. Timings include audit/logging, fresh final-window evaluation and baseline verification, and exclude one-time worker model loading. Source data, hardware and frozen source hashes are in the plans/manifests.

Fresh uses 1,024 unique selection windows for Llama and 1,152 for Qwen, versus eight for reuse. It also recomputes teacher/student prefixes. This intervention changes reuse together with unique text coverage; it does not establish a mechanism at equal data budget. The same two source draws and fixed audit windows are correlated observations, not independent population replicates.

## What this means for Section 9

The frozen P2 criterion failed. Withdraw the proposed operational explanation that avoiding repeated selection-window reuse substantially removes network optimism while leaving local unchanged in these settings. Candidate quality, objective mismatch and domain shift remain alternative questions, not established replacements. These observations do not prove that reuse can never cause optimism.
