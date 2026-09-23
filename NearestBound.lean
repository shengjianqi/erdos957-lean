import CirclePacking
import NearestGraph

/-! Unconditional degree and edge bounds for the planar closest-pair graph. -/

namespace Erdos957

/-- Every edge has the distance of any chosen minimum-distance pair. -/
theorem nearestGraph_adj_dist_eq {n : ℕ} (p : Fin n → Point)
    {ij : Fin n × Fin n} (hmin : isMinPair p ij)
    {i j : Fin n} (hadj : (nearestGraph p).Adj i j) :
    dist (p i) (p j) = pairDist p ij := by
  rcases (nearestGraph_adj_iff p i j).mp hadj with h | h
  · exact le_antisymm (h.2 ij hmin.1) (hmin.2 (i, j) h.1)
  · have heq := le_antisymm (h.2 ij hmin.1) (hmin.2 (j, i) h.1)
    simpa only [pairDist, dist_comm] using heq

/-- Every point in a distinct planar configuration has at most six neighbors
at the globally minimum pairwise distance. -/
theorem nearestGraph_degree_le_six {n : ℕ} (p : Fin n → Point)
    (hn : 2 ≤ n) (hp : Function.Injective p) (i : Fin n) :
    (nearestGraph p).degree i ≤ 6 := by
  classical
  obtain ⟨ij, hmin⟩ := exists_min_pair p hn
  let r := pairDist p ij
  have hr : 0 < r := pairDist_pos p hp hmin.1
  let N := ((nearestGraph p).neighborFinset i).image p
  have hcard : N.card = (nearestGraph p).degree i := by
    dsimp [N]
    rw [Finset.card_image_of_injective _ hp]
    exact (nearestGraph p).card_neighborFinset_eq_degree i
  have hradius : ∀ y ∈ N, dist (p i) y = r := by
    intro y hy
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
    exact nearestGraph_adj_dist_eq p hmin
      (((nearestGraph p).mem_neighborFinset i j).mp hj)
  have hsep : ∀ y ∈ N, ∀ z ∈ N, y ≠ z → r ≤ dist y z := by
    intro y hy z hz hyz
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
    have hjk : j ≠ k := fun heq => hyz (congrArg p heq)
    exact isMinPair_le_dist p hmin hjk
  rw [← hcard]
  exact circle_card_le_six N (p i) r hr hradius hsep

/-- The number of closest unordered pairs in a configuration of `n ≥ 2`
distinct points in the Euclidean plane is at most `3n`. -/
theorem sMin_le_three_mul {n : ℕ} (p : Fin n → Point)
    (hn : 2 ≤ n) (hp : Function.Injective p) :
    sMin p ≤ 3 * n :=
  sMin_le_three_mul_of_degree_le_six p
    (nearestGraph_degree_le_six p hn hp)

end Erdos957
