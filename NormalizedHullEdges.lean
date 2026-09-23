import HullExteriorAngles
import NormalizedTriangle
import NearestMetric

/-! Actual hull edges and telescoping identities in coordinates based on a
reversed consecutive edge, so the configuration lies below the real axis. -/

namespace Erdos957

theorem hullEdgeDirection_ne_zero {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (i : Fin h) : hullEdgeDirection p v i ≠ 0 := by
  have hi : i ≠ i + 1 := (cyclic_three_distinct hh i).1
  intro hz
  have heq : p (v (i + 1)) - p (v i) = 0 :=
    pointToComplex.injective (by simpa only [hullEdgeDirection, map_zero] using hz)
  exact hi (hv (hp (sub_eq_zero.mp heq))).symm

theorem hullEdgeDirection_div_norm_ge_one {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (i : Fin h) (hbase : (nearestGraph p).Adj (v i) (v (i + 1)))
    (j : Fin h) : 1 ≤ ‖hullEdgeDirection p v j / hullEdgeDirection p v i‖ := by
  obtain ⟨ab, hmin⟩ := exists_min_pair p hn
  have hr := pairDist_pos p hp hmin.1
  have hdist := nearestGraph_adj_dist_eq p hmin hbase
  have hsep := isMinPair_le_dist p hmin (hv.ne (cyclic_three_distinct hh j).1)
  have hnorm (k : Fin h) : ‖hullEdgeDirection p v k‖ =
      dist (p (v k)) (p (v (k + 1))) := by
    rw [hullEdgeDirection, pointToComplex.norm_map]
    simp only [dist_eq_norm, norm_sub_rev]
  rw [norm_div, hnorm, hnorm, hdist]
  exact (one_le_div₀ hr).mpr hsep

theorem normalized_hull_edge_sub {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (v : Fin h → Fin n) (i j : Fin h) :
    edgeCoordinate (p (v (i + 1))) (p (v i)) (p (v (j + 1))) -
        edgeCoordinate (p (v (i + 1))) (p (v i)) (p (v j)) =
      -(hullEdgeDirection p v j / hullEdgeDirection p v i) := by
  rw [edgeCoordinate_sub]
  have hden : pointToComplex (p (v i) - p (v (i + 1))) =
      -hullEdgeDirection p v i := by
    rw [hullEdgeDirection, ← map_neg]
    congr 1
    abel
  rw [hden, div_neg]
  rfl

theorem normalized_hull_left_two_sum {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (v : Fin h → Fin n) (i : Fin h) :
    edgeCoordinate (p (v (i + 1))) (p (v i)) (p (v (((i + 1) + 1) + 1))) =
      -(hullEdgeDirection p v (i + 1) / hullEdgeDirection p v i) -
        hullEdgeDirection p v ((i + 1) + 1) / hullEdgeDirection p v i := by
  let M := edgeCoordinate (p (v (i + 1))) (p (v i))
  have h1 := normalized_hull_edge_sub p v i (i + 1)
  have h2 := normalized_hull_edge_sub p v i ((i + 1) + 1)
  have hzero : M (p (v (i + 1))) = 0 := edgeCoordinate_self _ _
  change M (p (v ((i + 1) + 1))) - M (p (v (i + 1))) = _ at h1
  change M (p (v (((i + 1) + 1) + 1))) - M (p (v ((i + 1) + 1))) = _ at h2
  change M (p (v (((i + 1) + 1) + 1))) = _
  calc
    _ = (M (p (v (((i + 1) + 1) + 1))) - M (p (v ((i + 1) + 1)))) +
        (M (p (v ((i + 1) + 1))) - M (p (v (i + 1)))) + M (p (v (i + 1))) := by ring
    _ = _ := by rw [h1, h2, hzero]; ring

theorem normalized_hull_right_three_sum {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (v : Fin h → Fin n) (i : Fin h)
    (hne : p (v (i + 1)) ≠ p (v i)) :
    edgeCoordinate (p (v (i + 1))) (p (v i)) (p (v (((i - 1) - 1) - 1))) =
      1 + hullEdgeDirection p v (i - 1) / hullEdgeDirection p v i +
        hullEdgeDirection p v ((i - 1) - 1) / hullEdgeDirection p v i +
        hullEdgeDirection p v (((i - 1) - 1) - 1) / hullEdgeDirection p v i := by
  let M := edgeCoordinate (p (v (i + 1))) (p (v i))
  have h1 := normalized_hull_edge_sub p v i (i - 1)
  have h2 := normalized_hull_edge_sub p v i ((i - 1) - 1)
  have h3 := normalized_hull_edge_sub p v i (((i - 1) - 1) - 1)
  simp only [sub_add_cancel] at h1 h2 h3
  have hone : M (p (v i)) = 1 := edgeCoordinate_axis _ _ hne
  change M (p (v i)) - M (p (v (i - 1))) = _ at h1
  change M (p (v (i - 1))) - M (p (v ((i - 1) - 1))) = _ at h2
  change M (p (v ((i - 1) - 1))) - M (p (v (((i - 1) - 1) - 1))) = _ at h3
  change M (p (v (((i - 1) - 1) - 1))) = _
  calc
    _ = M (p (v i)) - (M (p (v i)) - M (p (v (i - 1)))) -
        (M (p (v (i - 1))) - M (p (v ((i - 1) - 1)))) -
        (M (p (v ((i - 1) - 1))) - M (p (v (((i - 1) - 1) - 1)))) := by ring
    _ = _ := by rw [h1, h2, h3, hone]; ring

end Erdos957
