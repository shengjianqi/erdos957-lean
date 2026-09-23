import LocalChargeAssembly

/-! Distance-preserving changes of coordinates preserve the finite graphs,
diameter endpoint indices, and local charge packets. -/

namespace Erdos957

theorem pairDist_eq_of_dist_eq {n : ℕ} (p p' : Fin n → Point)
    (hdist : ∀ i j, dist (p' i) (p' j) = dist (p i) (p j))
    (ij : Fin n × Fin n) : pairDist p' ij = pairDist p ij := hdist _ _

theorem isMinPair_iff_of_dist_eq {n : ℕ} (p p' : Fin n → Point)
    (hdist : ∀ i j, dist (p' i) (p' j) = dist (p i) (p j))
    (ij : Fin n × Fin n) : isMinPair p' ij ↔ isMinPair p ij := by
  simp only [isMinPair, pairDist, hdist]

theorem isMaxPair_iff_of_dist_eq {n : ℕ} (p p' : Fin n → Point)
    (hdist : ∀ i j, dist (p' i) (p' j) = dist (p i) (p j))
    (ij : Fin n × Fin n) : isMaxPair p' ij ↔ isMaxPair p ij := by
  simp only [isMaxPair, pairDist, hdist]

theorem nearestGraph_eq_of_dist_eq {n : ℕ} (p p' : Fin n → Point)
    (hdist : ∀ i j, dist (p' i) (p' j) = dist (p i) (p j)) :
    nearestGraph p' = nearestGraph p := by
  ext i j
  simp only [nearestGraph_adj_iff, isMinPair_iff_of_dist_eq p p' hdist]

theorem diameterGraph_eq_of_dist_eq {n : ℕ} (p p' : Fin n → Point)
    (hdist : ∀ i j, dist (p' i) (p' j) = dist (p i) (p j)) :
    diameterGraph p' = diameterGraph p := by
  ext i j
  simp only [diameterGraph_adj_iff, isMaxPair_iff_of_dist_eq p p' hdist]

theorem nearestGraph_degree_eq_of_dist_eq {n : ℕ} (p p' : Fin n → Point)
    (hdist : ∀ i j, dist (p' i) (p' j) = dist (p i) (p j)) (u : Fin n) :
    (nearestGraph p').degree u = (nearestGraph p).degree u := by
  simp only [← SimpleGraph.ncard_neighborSet, nearestGraph_eq_of_dist_eq p p' hdist]

theorem diameterEndpoints_eq_of_dist_eq {n : ℕ} (p p' : Fin n → Point)
    (hdist : ∀ i j, dist (p' i) (p' j) = dist (p i) (p j)) :
    diameterEndpoints p' = diameterEndpoints p := by
  ext i
  rw [mem_diameterEndpoints_iff_exists_adj, mem_diameterEndpoints_iff_exists_adj,
    diameterGraph_eq_of_dist_eq p p' hdist]

theorem chargeDonors_eq_of_dist_eq {n : ℕ} (p p' : Fin n → Point)
    (hdist : ∀ i j, dist (p' i) (p' j) = dist (p i) (p j))
    (bad : Finset (Fin n)) : chargeDonors p' bad = chargeDonors p bad := by
  simp only [chargeDonors, diameterEndpoints_eq_of_dist_eq p p' hdist,
    nearestGraph_degree_eq_of_dist_eq p p' hdist]

/-- Transport a checked packet back from a congruent configuration without
changing its receiver indices. This asserts no geometric side or capacity
property beyond the original packet fields. -/
noncomputable def LocalChargePacket.of_dist_eq {n : ℕ}
    (p p' : Fin n → Point)
    (hdist : ∀ i j, dist (p' i) (p' j) = dist (p i) (p j))
    {u : Fin n} (packet : LocalChargePacket p' u) : LocalChargePacket p u := by
  have hG := nearestGraph_eq_of_dist_eq p p' hdist
  have hD := diameterEndpoints_eq_of_dist_eq p p' hdist
  have hdeg := nearestGraph_degree_eq_of_dist_eq p p' hdist
  exact {
    left := packet.left
    right := packet.right
    left_outside := by simpa only [hD] using packet.left_outside
    right_outside := by simpa only [hD] using packet.right_outside
    left_degree := by simpa only [hdeg] using packet.left_degree
    right_degree := by simpa only [hdeg] using packet.right_degree
    repeated_degree := by simpa only [hdeg] using packet.repeated_degree
    left_reachable := by simpa only [hG] using packet.left_reachable
    right_reachable := by simpa only [hG] using packet.right_reachable
  }

theorem LocalChargePacket.of_dist_eq_weight {n : ℕ}
    (p p' : Fin n → Point)
    (hdist : ∀ i j, dist (p' i) (p' j) = dist (p i) (p j))
    {u : Fin n} (packet : LocalChargePacket p' u) (k : Fin n) :
    (packet.of_dist_eq p p' hdist).weight k = packet.weight k := rfl

end Erdos957
