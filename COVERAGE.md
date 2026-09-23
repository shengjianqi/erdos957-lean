# Final coverage: Erdős 957 / JSP-000797

## Statement correspondence

`Point` is `EuclideanSpace ℝ (Fin 2)`. An injective map from Fin n represents
n distinct points. `pairs n` contains exactly index pairs i<j, so each unordered
pair of distinct points appears once. `isMinPair` and `isMaxPair` compare against
all such pairs. `sMin` and `sMax` count every global minimum/maximum tie.

The published mathematical source establishes the 9/8 leading coefficient with
a uniform O(n) error for these counts. The formal statement gives the explicit
constant25200 and therefore the same asymptotic upper bound. It makes no claim
that25200 is optimal or that this package supplies a new mathematical discovery.

## Complete receiver coverage

| Receiver case | Final interface |
| --- | --- |
| Degree<=4, all certified rules | certified_family_receiver_capacity_of_degree_le_four |
| Degree5, diameter neighbor exists, actual supporting family | supporting_family_degree_five_mixed_capacity |
| Degree5, no diameter neighbor, arbitrary certified family | certified_family_degree_five_capacity_of_no_diameter_neighbor |
| Degree6 | certified_family_receiver_total_eq_zero_of_degree_six |
| All degrees, concrete supporting family | supporting_family_receiver_capacity |

The degree bound of six is proved geometrically. Every sum in this assembly uses
the same supplied supporting family. No rule-specific capacity is silently
substituted for the full simultaneous sum.

## All configurations

| Configuration | Certificate and exception count |
| --- | --- |
| n<=1681 | bad=D; no eligible donors; zero charge; cardinality<=1681 |
| n>1681, collinear | bad=D; zero charge; cardinality<=2 |
| n>1681, noncollinear | proved oriented hull exists; certified supporting family; cardinality<=25200 |

`exists_uniform_charge_certificate` covers every injective configuration,
including n=0,1. Product statements require n>=2 because shortest/longest pairs
are the quantities being studied.

## Final targets

- `uniform_charging_bound`: sMin+2D<=3n+25200.
- `erdos957_product_bound`: sMin*sMax<=(9/8)n²+25200n.
- `erdos957_quantitative`: the original project's QuantitativeBound proposition.
- `erdos957_asymptotic`: for every ε>0, one threshold works for all configurations.

No previously identified mathematical obligation remains in these targets.
External review, attribution, publication, priority and award acceptance are
separate processes. Publication and review do not themselves establish award acceptance.

Full build2833 jobs; axiom audit776 declarations; only the three standard axioms.
See VERIFICATION.md for exact verification limits. 
