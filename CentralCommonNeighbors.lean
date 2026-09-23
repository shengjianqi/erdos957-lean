import CentralProjection
import HexagonCompletion
import BoundaryDegree
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-! Degree slack for any common neighbor of a central nearest edge at a
diameter endpoint. -/

namespace Erdos957

/-- A common nearest neighbor of a diameter endpoint and its central nearest
neighbor has degree at most five. The central cone bounds rule out the
reflected neighbor that degree six would force across the endpoint's strict
supporting half-plane. -/
theorem common_neighbor_degree_le_five_of_central {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {u j v a : Fin n}
    (hdiam : (diameterGraph p).Adj u j)
    (huv : (nearestGraph p).Adj u v)
    (hvlo : -Real.pi / 6 < halfplaneArg (p u) (p j - p u) (p v))
    (hvhi : halfplaneArg (p u) (p j - p u) (p v) < Real.pi / 6)
    (hua : (nearestGraph p).Adj u a)
    (hva : (nearestGraph p).Adj v a) :
    (nearestGraph p).degree a ≤ 5 := by
  by_contra hnot
  have hadeg : (nearestGraph p).degree a = 6 := by
    have hle := nearestGraph_degree_le_six p hn hp a
    omega
  obtain ⟨b, _hba, _hab, hub, hsum⟩ :=
    degree_six_triangle_completion p hn hp hadeg hua.symm hva.symm huv
  obtain ⟨ij, hmin⟩ := exists_min_pair p hn
  let r := pairDist p ij
  have hr : 0 < r := pairDist_pos p hp hmin.1
  have hvdist : dist (p u) (p v) = r :=
    nearestGraph_adj_dist_eq p hmin huv
  have hadist : dist (p u) (p a) = r :=
    nearestGraph_adj_dist_eq p hmin hua
  have hvadist : dist (p v) (p a) = r :=
    nearestGraph_adj_dist_eq p hmin hva
  have hvhalf : 0 < inner ℝ (p j - p u) (p v - p u) :=
    diameter_neighbor_inner_pos_of_other p hp hdiam
      ((nearestGraph p).ne_of_adj huv)
  have hahalf : 0 < inner ℝ (p j - p u) (p a - p u) :=
    diameter_neighbor_inner_pos_of_other p hp hdiam
      ((nearestGraph p).ne_of_adj hua)
  have hbhalf : 0 < inner ℝ (p j - p u) (p b - p u) :=
    diameter_neighbor_inner_pos_of_other p hp hdiam
      ((nearestGraph p).ne_of_adj hub)
  have hproj : inner ℝ (p j - p u) (p a - p u) <
      inner ℝ (p j - p u) (p v - p u) :=
    central_neighbor_inner_gt (p u) (p j - p u) (p v) (p a) r
      hr hvdist hadist hvadist.symm.le hvhalf hahalf hvlo hvhi
  have hvec : p b - p u = (p a - p u) - (p v - p u) := by
    have hb : p b = p a + p u - p v := by
      calc
        p b = (p v + p b) - p v := by abel
        _ = (p a + p u) - p v := by rw [hsum]
    rw [hb]
    abel
  have hinner : inner ℝ (p j - p u) (p b - p u) =
      inner ℝ (p j - p u) (p a - p u) -
        inner ℝ (p j - p u) (p v - p u) := by
    rw [hvec, inner_sub_right]
  linarith

end Erdos957
