import HullSupport
import BoundaryDegree
import DiameterHull
import DiameterBound

/-! The closest-pair degree bound for every extreme hull vertex. -/

namespace Erdos957

/-- A strict inward supporting normal gives degree at most three. -/
theorem nearestGraph_degree_le_three_of_inward_normal {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    (u : Fin n) (axis : Point)
    (hinward : ∀ j : Fin n, j ≠ u → 0 < inner ℝ axis (p j - p u)) :
    (nearestGraph p).degree u ≤ 3 := by
  classical
  obtain ⟨ij, hmin⟩ := exists_min_pair p hn
  let r := pairDist p ij
  have hr : 0 < r := pairDist_pos p hp hmin.1
  let N := ((nearestGraph p).neighborFinset u).image p
  have hcard : N.card = (nearestGraph p).degree u := by
    dsimp [N]
    rw [Finset.card_image_of_injective _ hp]
    exact (nearestGraph p).card_neighborFinset_eq_degree u
  have hradius : ∀ y ∈ N, dist (p u) y = r := by
    intro y hy
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
    exact nearestGraph_adj_dist_eq p hmin
      (((nearestGraph p).mem_neighborFinset u j).mp hj)
  have hsep : ∀ y ∈ N, ∀ z ∈ N, y ≠ z → r ≤ dist y z := by
    intro y hy z hz hyz
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
    exact isMinPair_le_dist p hmin (fun h => hyz (congrArg p h))
  have hhalf : ∀ y ∈ N, 0 < inner ℝ axis (y - p u) := by
    intro y hy
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
    have hadj := ((nearestGraph p).mem_neighborFinset u j).mp hj
    exact hinward j hadj.ne.symm
  rw [← hcard]
  exact circle_card_le_three_in_halfplane N (p u) axis r hr hradius hsep hhalf

/-- Every extreme vertex of the actual convex hull has closest-pair degree
at most three, including vertices that are not diameter endpoints. -/
theorem nearestGraph_degree_le_three_of_hullVertex {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    (u : Fin n) (hu : u ∈ hullVertexIndices p) :
    (nearestGraph p).degree u ≤ 3 := by
  classical
  have hext : p u ∈ (convexHull ℝ (Set.range p)).extremePoints ℝ :=
    (Finset.mem_filter.mp hu).2
  obtain ⟨axis, _, haxis⟩ := hull_extreme_inward_normal p hn hp u hext
  exact nearestGraph_degree_le_three_of_inward_normal p hn hp u axis haxis

/-- Weighted handshaking with the full hull-vertex count. -/
theorem nearestGraph_hull_weighted_handshake {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p) :
    2 * sMin p + 3 * hullVertexCount p ≤ 6 * n := by
  classical
  let H := hullVertexIndices p
  have hpoint (i : Fin n) :
      (nearestGraph p).degree i + (if i ∈ H then 3 else 0) ≤ 6 := by
    by_cases hi : i ∈ H
    · simp only [hi, ↓reduceIte]
      have h3 := nearestGraph_degree_le_three_of_hullVertex p hn hp i hi
      omega
    · simpa only [hi, ↓reduceIte, add_zero] using nearestGraph_degree_le_six p hn hp i
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpoint i)
  have hcredit : (∑ i : Fin n, if i ∈ H then (3 : ℕ) else 0) = 3 * H.card := by
    simp [mul_comm]
  rw [Finset.sum_add_distrib, nearestGraph_handshake p, hcredit] at hsum
  simpa [H, hullVertexCount, mul_comm] using hsum

/-- If there are sufficiently many hull vertices compared with diameter
endpoints, the desired counting bound follows without any charge transfer. -/
theorem charging_bound_of_many_hull_vertices {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    (hcounts : 4 * diameterEndpointCount p ≤ 3 * hullVertexCount p) :
    sMin p + 2 * diameterEndpointCount p ≤ 3 * n := by
  have h := nearestGraph_hull_weighted_handshake p hn hp
  omega

/-- In that regime even the linear error term is unnecessary. -/
theorem product_bound_of_many_hull_vertices {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    (hcounts : 4 * diameterEndpointCount p ≤ 3 * hullVertexCount p) :
    8 * sMin p * sMax p ≤ 9 * n ^ 2 := by
  have h := ExtremeDistances.product_bound_nat n (sMin p) (sMax p)
    (diameterEndpointCount p) 0 (sMax_le_diameterEndpointCount p hp)
    (diameterEndpointCount_le p)
    (by simpa using charging_bound_of_many_hull_vertices p hn hp hcounts)
  simpa using h

end Erdos957
