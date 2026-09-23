# Attribution and provenance

## Mathematical source

Adrian Dumitrescu, *A Product Inequality for Extreme Distances*, SoCG 2019,
LIPIcs 129, 30:1-30:12, DOI [10.4230/LIPIcs.SoCG.2019.30](https://doi.org/10.4230/LIPIcs.SoCG.2019.30).
This formalization concerns the published upper bound, not a new discovery of
that mathematical result.

## Formalization project

- Project owner and submitting contributor: [shengjianqi](https://github.com/shengjianqi).
- The formalization was developed through user-directed OpenAI Codex/ChatGPT
  sessions. Proof construction, Lean implementation, repairs and checks used AI
  assistance. This is not a claim of a wholly manually written proof.
- The owner supplied the Case 4 two-step patch and companion archive dated
  2026-09-22. On 2026-09-23 the owner confirmed that these were generated in the
  owner's own AI conversation, rather than supplied by a separate author.
- The candidate was checked separately, repaired and integrated. Repairs included
  dependent packet transport, reflected index orientation, cyclic neighbor
  cancellation and the backward two-edge classification. Subsequent work closed
  low-degree and degree-five receiver capacities and the unconditional theorem.

Historical input names:

```text
erdos957-case4-two-step-20260922.patch
erdos957-lean-attempt-case4-two-step-20260922.zip
```

This initial repository publication records the completed source. Its initial
commit is not a reconstruction of the earlier unpublished editing history.
No earlier public timestamp or independent human certification is asserted.

## Dependencies and prior work

Lean, Mathlib and the packages recorded in `lake-manifest.json` retain their
respective contributor attribution and licenses. Their source and build artifacts
are not redistributed here.

The distinct public `plby/lean-proofs` formalization is disclosed in
[RELATED_WORK.md](RELATED_WORK.md). Comparing whole-file hashes does not establish
independent authorship or absence of partial reuse; no such certification is claimed.
