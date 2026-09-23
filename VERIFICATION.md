# Publication verification report

Date: 2026-09-23. Problem: Erdős #957 / JSP-000797.

## Result and checked version

The quantitative and asymptotic upper-bound targets passed the Lean checks below.
The exact 227 root Lean files, toolchain file and dependency manifest checked here
are identified by `SOURCE_SHA256.txt`. The publication retains those source bytes;
`.gitattributes` disables automatic line-ending conversion so checksums are stable
across platforms.

The source is the completed local formalization. No mathematical proof file was
changed for publication. The Mathlib declaration and manifest input revision were
both fixed to `067a2c89ad91a79c38006b1d0e8137533fadb81b`; the resolved dependency
revision is the same as in the development verification.

This report and its logs are shipped alongside the checked source in the selected
publication commit. It does not assert an earlier public completion timestamp.

## Mathematical correspondence

For every natural `n >= 2` and injective
`p : Fin n -> EuclideanSpace ℝ (Fin 2)`,

```text
sMin(p) * sMax(p) <= (9/8)*n^2 + 25200*n.
```

Both quantities count unordered pairs of distinct points attaining the global
minimum or maximum distance. `Foundations.lean` fixes these definitions.
The epsilon formulation has one threshold for every configuration, for each
positive epsilon. `FinalStatementCheck.lean` checks both explicitly expanded
statements and prints the three final target signatures and axiom dependencies.

Mathematical source: Adrian Dumitrescu, *A Product Inequality for Extreme
Distances*, SoCG 2019, Theorem 1, page 30:1,
[DOI 10.4230/LIPIcs.SoCG.2019.30](https://doi.org/10.4230/LIPIcs.SoCG.2019.30).
Mathematical discovery credit belongs to the published source. The explicit
linear coefficient is not claimed optimal. See `COVERAGE.md` for case coverage.

## Execution evidence

- Lean: `leanprover/lean4:v4.35.0-rc2`.
- Mathlib: `067a2c89ad91a79c38006b1d0e8137533fadb81b`.
- Full project build: **2833 jobs, exit 0**, in `verification/BUILD.log`.
- Portable Windows reproduction script `verify.ps1`: build, audit and expanded
  statement commands passed. The combined output is `verification/VERIFY.log`.
- Audit: **776 distinct declarations**, all 776 entries requested by `Audit.lean`
  found in the output; **zero missing entries**.
- Every printed axiom set is a subset of `propext`, `Classical.choice`,
  `Quot.sound`. The final three targets each report exactly those three axioms.
- Extracted audit records preserve multiline axiom lists in `verification/AXIOMS.log`.
- Final signatures and target axioms: `verification/FINAL_STATEMENT_CHECK.log`.
- Machine-readable summary: `verification/SUMMARY.json`.
- Source keyword check found no proof placeholders, custom axiom declarations,
  `unsafe`, or `native_decide`. An occurrence of the English word "admit" is in
  a comment in `TruncatedCirclePacking.lean`, not a proof command.

The default `Lean957` library imports all 224 proof modules. `Audit.lean` and
`FinalStatementCheck.lean` are separate checks, not inferred from build success.

## Reproduction

Install elan, check out the selected commit in a new directory and keep the
toolchain and dependency manifest unchanged:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
lake env lean FinalStatementCheck.lean
```

On Windows PowerShell, after dependencies/cache are available, `./verify.ps1`
obtains `LEAN_PATH` from `lake env` and uses `elan which lean` to locate the
pinned executable. The script does not require the development machine's local
toolchain directory. Its commands check failure codes before continuing.

## Verification limits

Publication verification used a new project build directory: project artifacts
were rebuilt from source. Installed, pinned dependency packages and their build
artifacts were reused from the development environment. The nine dependency Git
repositories had no tracked modifications when inspected. This is **not** a
fresh-machine or fresh-dependency rebuild.

The checks trust the stated Lean implementation and its pinned dependencies.
No separate kernel replay checker, alternative theorem prover, independent human
certification or organizer reproduction is claimed. Build logs include linter
warnings for unused arguments, tactics and style; they are not proof errors.

AI source review inspected the final assembly interfaces and publication
materials. It is reported as AI review, not independent human verification.

The other public formalization disclosed in `RELATED_WORK.md` was not rebuilt
as part of this check. Public priority, authorship evaluation and award acceptance
are separate from this local proof verification.
