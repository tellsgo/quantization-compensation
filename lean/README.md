# Lean source artifact for manuscript v6.4

**When Does Compensating Inherited Quantization Error Help?**  
**Mean-Square Guarantees for Layer-Wise Quantization and Their Limits**

This source package contains **96 scientific modules and 969 explicitly named theorem declarations**, including auxiliary lemmas. This is a declaration count, not a count of scientific results. The package is a reproduction artifact with scoped claim mappings; it is not a claim that every theorem in the manuscript has been formalized.

The manuscript identity is SHA-256 `2365e301dc85f4b405c95a93a84aa232135a20fadf66ef516eeddbcad4bdd251`. Numbering is 1–27 in v6.4, including the appended examples. Earlier numbers embedded in historical module or theorem names are retained to avoid changing formal identifiers; `CLAIMS.json` supplies the current map.

## Build and verify

Lean is pinned to **4.34.1** and Mathlib to **d13f23b723b8a846827a245b89c10fc7d3f11612**. The lockfile pins transitive dependencies. With Elan, Git and Python 3 available, run from this directory:

```sh
lake exe cache get
lake build
python3 scripts/check.py
```

The first command only fetches dependency caches. No project binaries or dependency caches are distributed. Bare `lake build` builds every scientific source and the central axiom audit. On memory-constrained systems, `python3 scripts/build_serial.py` builds modules in dependency order before the bare build; the scientific checks are identical. Each Lean elaboration is single-threaded with an 8192 MB memory limit.

`python3 scripts/check.py` may also be called by its path from another working directory. It verifies source hashes, the complete explicit declaration inventory, axiom dependencies, positive controls and substantive negative controls. Allowed axioms are only `propext`, `Classical.choice` and `Quot.sound`. A missing import or resource failure is not counted as a valid negative control. Standard elaboration and Lean kernel checking are used; no external proof checker is claimed.

## What the package establishes

- Actual prescribed-error scalar/matrix recursions, residual identities and legal counterexamples, plus exact finite-codebook minimizers.
- Linear network moment comparison under explicitly stated finite-support conditional moments, including zero-strength bypass and separate probability spaces. Gram legality is needed only on positive-mass QEP atoms at positive strength; zero-mass atoms and zero-strength layers may be singular. General continuous-law output integrability remains a paper argument.
- Actual scalar continuous-dither ReLU counterexample; actual continuous finite-grid laws, matrix losses, random-history gap and overload cross bounds under explicit integrability and rank assumptions. Gap strengths are fixed; energy/cross formulas may use upstream-history strengths independent of fresh dither.
- Actual sequential feedback process, fixed-parameter covariance and energy, matched-Gram overload; a separate measurable random-upstream standardized-innovation joint law. Matched Gram factorization and the single-row teacher-loss projection identity remain explicit premises.
- Algebraic cell identities and commutator/defect propagation. The new commutator code assumes a bilinear bound; the defect kernel assumes its input matrix recurrences. Neither is a formal proof of the full stochastic Theorem 15, nor a bridge from the bilinear bound to Mathlib’s operator norm.

See [SCOPE.html](SCOPE.html) for the complete 27-item map and the finite/general, fixed/random, algebra/expectation boundaries. [CLAIMS.json](CLAIMS.json) maps every module and every explicit theorem; [DECLARATIONS.json](DECLARATIONS.json) is the exhaustive audit inventory.

## Manuscript qualifications

The source artifact is bound to the v6.4 mother manuscript. All five required v6.3 review items close: trained-model scope, depth-qualified gain comparison, distinction between actual rounding and sampled/enumerated errors, paired-teacher gain uncertainty, and descriptive cross-implementation agreement. The targeted three overload references were also corrected; a separate inherited navigation issue is tracked in the current review.

Independent deterministic checks recomputed all 28 paired gain standard errors from saved teacher records and matched 8,400 teacher-level values retained by the previous independent replay. No new Monte Carlo study was run. Actual NumPy point estimates are unchanged; some saved Python comparison fields were refreshed to already retained independent-t outputs. The unused unpaired diagnostic must not be confused with the previous plotted normalized unpaired uncertainty.

The TSP main document and supplement were independently reviewed against the mother. The 27 numbered statements correspond as 22 plus 5; all 17 line-break substitutions are applied, and five regenerated TeX files match the received source bytes. Cross-file reference targets and compiled text were checked. Current naming and navigation findings remain in REBINDING.json. This is not a submission-ready release or whole-manuscript scientific acceptance. Compression and journal formatting are outside this update.

The mother retains all 27 numbered statements, all 14 proof bodies and the bibliography byte-for-byte from v6.3. CLAIMS.json is the mother-manuscript mapping, not a separate claim map for the TSP derivative. Proposition 9, Corollary 10, Example 11 and the weighted-projection notes are still NOT formalized. Numerical illustrations are not Lean proofs. Numerical code remains separate from this Lean source ZIP.

All 110 Lean source files, build configuration, verification scripts and the historical actual source-build receipt remain byte-identical. This metadata update performs no Lean compilation, source edits, new formalization, experiment or submission. Earlier tracked mathematical closures remain valid within their recorded scope; current local editorial findings do not reopen them.

The older eleven-module artifact is preserved separately. No old duplicate of `QepLinearOrder` is included. Historical supporting variants are explicitly labeled; they do not silently strengthen current claims.

## Provenance

`PROVENANCE.json` maps frozen source hashes to distributable source hashes. Only comments and inline axiom-print commands were removed; mathematical tokens are preserved. `VALIDATION.json` is preserved byte-for-byte from the accepted v4.1 source package: its Lean build and proof checks were performed on 2026-10-04 (UTC). All scientific sources, controls, build configuration and verification scripts remain byte-identical. No Lean build was rerun for this manuscript-only update. `REBINDING.json` records the v6.4 manuscript identity and retained 27-item numbering, the accepted v6.3 metadata predecessor and the inherited v4.1 source-build validation; `SHA256SUMS` covers the current distributable files. Raw development logs and machine-specific receipts are retained separately from this public source distribution.
