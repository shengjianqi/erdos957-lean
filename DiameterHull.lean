import DiameterExtreme
import DiameterSupport
import Reduction

/-! Convex-hull counts and strict supporting directions for diameter endpoints. -/

namespace Erdos957

/-- Indices of points that are extreme in the convex hull of the configuration. -/
noncomputable def hullVertexIndices {n : ℕ} (p : Fin n → Point) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i =>
    p i ∈ (convexHull ℝ (Set.range p)).extremePoints ℝ

noncomputable def hullVertexCount {n : ℕ} (p : Fin n → Point) : ℕ :=
  (hullVertexIndices p).card

/-- Every diameter endpoint is a vertex of the convex hull. -/
theorem diameterEndpoints_subset_hullVertexIndices {n : ℕ}
    (p : Fin n → Point) (hp : Function.Injective p) :
    diameterEndpoints p ⊆ hullVertexIndices p := by
  classical
  intro i hi
  obtain ⟨ij, hmax, hi⟩ := (Finset.mem_filter.mp hi).2
  have hvertices := isMaxPair_endpoints_extreme p hp hmax
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ i, ?_⟩
  rcases hi with hi | hi
  · simpa only [hi] using hvertices.1
  · simpa only [hi] using hvertices.2

/-- The diameter endpoint count is at most the number of hull vertices. -/
theorem diameterEndpointCount_le_hullVertexCount {n : ℕ}
    (p : Fin n → Point) (hp : Function.Injective p) :
    diameterEndpointCount p ≤ hullVertexCount p :=
  Finset.card_le_card (diameterEndpoints_subset_hullVertexIndices p hp)

theorem hullVertexCount_le {n : ℕ} (p : Fin n → Point) :
    hullVertexCount p ≤ n := by
  classical
  unfold hullVertexCount hullVertexIndices
  calc
    _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
    _ = n := by simp

/-- A diameter endpoint strictly maximizes the radial linear functional among
all other points in the configuration. -/
theorem isMaxPair_left_support_strict {n : ℕ} (p : Fin n → Point)
    (hp : Function.Injective p) {ij : Fin n × Fin n}
    (hmax : isMaxPair p ij) (k : Fin n) (hk : k ≠ ij.1) :
    inner ℝ (p ij.1 - p ij.2) (p k) <
      inner ℝ (p ij.1 - p ij.2) (p ij.1) := by
  apply farthest_support_strict (p ij.1) (p ij.2) (p k)
  · have h := dist_le_of_isMaxPair p hmax ij.2 k
    simpa only [pairDist, dist_comm] using h
  · exact fun heq => hk (hp heq)

end Erdos957
