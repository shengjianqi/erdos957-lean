import DiameterHull

/-! Interior configuration points cannot be hull vertices or diameter endpoints. -/

namespace Erdos957

/-- A point in the interior of the configuration's convex hull is not a hull
vertex. No injectivity or cardinality hypothesis is needed. -/
theorem interior_not_hullVertexIndices {n : ℕ} (p : Fin n → Point)
    (k : Fin n)
    (hinner : p k ∈ interior (convexHull ℝ (Set.range p))) :
    k ∉ hullVertexIndices p := by
  classical
  intro hk
  have hext : p k ∈ (convexHull ℝ (Set.range p)).extremePoints ℝ :=
    (Finset.mem_filter.mp hk).2
  exact Set.disjoint_left.mp
    (disjoint_interior_extremePoints (convexHull ℝ (Set.range p))) hinner hext

/-- An interior point cannot be a diameter endpoint in an injective finite
configuration. -/
theorem interior_not_diameterEndpoints {n : ℕ} (p : Fin n → Point)
    (hp : Function.Injective p) (k : Fin n)
    (hinner : p k ∈ interior (convexHull ℝ (Set.range p))) :
    k ∉ diameterEndpoints p := by
  intro hk
  exact interior_not_hullVertexIndices p k hinner
    ((diameterEndpoints_subset_hullVertexIndices p hp) hk)

end Erdos957
