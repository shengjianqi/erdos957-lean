# Related formalization

The public repository [plby/lean-proofs](https://github.com/plby/lean-proofs)
contains a formalization of the same Erdős #957 upper-bound result at commit
`8822f7ddef30fadbd92e1c6ab4ed897af356af5e`:

[Erdos957.lean](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos957.lean).

Prize catalog PRs [#1330](https://github.com/TheJustinSunPrize/awards/pull/1330)
and [#4102](https://github.com/TheJustinSunPrize/awards/pull/4102) reference that
same fixed source. They were open and unmerged when checked on 2026-09-23.
Their submitters describe themselves as catalog editors rather than proof authors.

The target overlaps: unordered closest/farthest pair multiplicities in finite
Euclidean planar sets, with uniform `9/8*n^2 + O(n)` upper bound. The present
project uses injective `Fin n` configurations and its own certificate interfaces.
Its stated global coefficient of the linear term is 25200. The cited source's
`Assembly.lean` chooses `41209^3 + 1260` globally, while obtaining 1260 for its
large-distance-ratio branch. No optimality or new mathematical discovery is
claimed for the present constant.

An exact download check of that entry and its Erdős957 subdirectory matched all
89 Git blob hashes to the pinned Git tree. Comparison to the present project's
227 root Lean files found no identical whole file, including after whitespace
removal. This limited comparison neither certifies independent creation nor
rules out partial overlap. The other project's complete build and transitive
axiom audit were not reproduced in this check.

This repository makes no first-public-formalization priority claim. Submission,
attribution, priority and award eligibility remain matters for external review.
