import NearestBound

/-! Recovering closest-pair graph adjacency from a distance equality. -/

namespace Erdos957

/-- A canonically oriented pair attaining the minimum distance is a
minimum-distance pair. -/
theorem isMinPair_of_dist_eq {n : ℕ} (p : Fin n → Point)
    {ij : Fin n × Fin n} (hmin : isMinPair p ij)
    {i j : Fin n} (hij : i < j)
    (heq : dist (p i) (p j) = pairDist p ij) :
    isMinPair p (i, j) := by
  refine ⟨mem_pairs_iff.mpr hij, ?_⟩
  intro kl hkl
  change dist (p i) (p j) ≤ pairDist p kl
  rw [heq]
  exact hmin.2 kl hkl

/-- With distinct points, attaining the chosen positive minimum distance
is equivalent to adjacency in the closest-pair graph. -/
theorem nearestGraph_adj_iff_dist_eq {n : ℕ} (p : Fin n → Point)
    (hp : Function.Injective p) {ij : Fin n × Fin n}
    (hmin : isMinPair p ij) (i j : Fin n) :
    (nearestGraph p).Adj i j ↔ dist (p i) (p j) = pairDist p ij := by
  constructor
  · exact nearestGraph_adj_dist_eq p hmin
  · intro heq
    have hne : i ≠ j := by
      intro hij
      have hr := pairDist_pos p hp hmin.1
      rw [hij, dist_self] at heq
      linarith
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact (nearestGraph_adj_iff p i j).mpr
        (Or.inl (isMinPair_of_dist_eq p hmin hlt heq))
    · have heq' : dist (p j) (p i) = pairDist p ij := by
        simpa only [dist_comm] using heq
      exact (nearestGraph_adj_iff p i j).mpr
        (Or.inr (isMinPair_of_dist_eq p hmin hgt heq'))

end Erdos957
