# Erdős 957: an extreme-distance product bound in Lean

This repository contains the Lean formalization developed in the project directed
by [shengjianqi](https://github.com/shengjianqi), with OpenAI Codex/ChatGPT assistance.
For every injective configuration of `n >= 2` points in the Euclidean plane,
counting unordered pairs,

```text
sMin * sMax <= (9/8) * n^2 + 25200 * n.
```

The mathematical upper-bound result is due to Adrian Dumitrescu (2019),
[A Product Inequality for Extreme Distances](https://doi.org/10.4230/LIPIcs.SoCG.2019.30).
The problem identifiers are **Erdős #957 / JSP-000797**.

## Main theorems

Import `Erdos957Complete`:

- `Erdos957.erdos957_product_bound`: the explicit inequality above.
- `Erdos957.erdos957_quantitative`: a uniform linear-error bound.
- `Erdos957.erdos957_asymptotic`: for every positive epsilon, one threshold works
  for all configurations, giving the coefficient `9/8 + epsilon`.

The final statements require only `n >= 2` and injectivity. Small sizes,
collinearity, actual hull construction and all receiver capacities are handled
inside the proof. `Foundations.lean` defines the point type and pair counts;
`FinalStatementCheck.lean` checks explicitly expanded statements.

## Reproduce

Install [elan](https://github.com/leanprover/elan) and put `lake` on PATH.
Keep `lean-toolchain` and `lake-manifest.json` unchanged. From this directory:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
lake env lean FinalStatementCheck.lean
```

`lake exe cache get` fetches the pinned dependencies and their available Mathlib
build cache. It is an acceleration step; missing cache entries can be built from
source. Do not run `lake update` to reproduce this version.

On Windows PowerShell, after the cache step, use `./verify.ps1` if necessary.
This script obtains the Lean module path from Lake and invokes the pinned Lean
executable directly, avoiding the development host's child-environment issue.

- Lean: `leanprover/lean4:v4.35.0-rc2`.
- Mathlib: `067a2c89ad91a79c38006b1d0e8137533fadb81b`, pinned in both build
  configuration and lockfile.
- Default build target: `Lean957`, importing all 224 proof modules.
- `Audit.lean` and `FinalStatementCheck.lean` run separately after the build.

See [VERIFICATION.md](VERIFICATION.md) for the checks actually performed and
their limits; [COVERAGE.md](COVERAGE.md) maps the geometric cases to theorems.

## Proof outline

1. Construct certified donor packets on a supporting hull.
2. Prove simultaneous weighted capacity for every receiver degree.
3. Obtain a concrete charge certificate, with at most 25200 exceptional points.
4. Cover small and collinear sets separately within the same uniform bound.
5. Derive `sMin + 2D <= 3n + 25200` and combine it with `sMax <= D <= n`.

## Attribution and related work

See [ATTRIBUTION.md](ATTRIBUTION.md) for authorship, AI assistance and Case 4
provenance, and [RELATED_WORK.md](RELATED_WORK.md) for a prior public formalization
of the same mathematical result. This repository does not claim the original
mathematical discovery, first-public-formalization priority, or an award decision.
The constant 25200 is not claimed optimal.

No additional open-source license is granted by this initial publication.
Lean, Mathlib and other dependencies retain their own licenses and are not vendored.
