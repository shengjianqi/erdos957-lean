import HexagonCompletion
import HullEdgeBeyond
import NearestBound
import Mathlib.Tactic.Abel

/-! An outer common neighbor of a six-degree shared edge has degree slack
when its opposite vertex lies on the actual convex hull. -/

namespace Erdos957

/-- The outer completion point `b` cannot have degree six: completing the
triangle at `b` would put another configuration point on the ray beyond the
extreme hull vertex `w`. -/
theorem shared_outer_neighbor_degree_le_five {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    {u w v b : Fin n}
    (hvw : (nearestGraph p).Adj v w)
    (hvb : (nearestGraph p).Adj v b)
    (hwb : (nearestGraph p).Adj w b)
    (hidentity : p u + p b = p v + p w)
    (hw : w ∈ hullVertexIndices p) (hwu : w ≠ u) :
    (nearestGraph p).degree b ≤ 5 := by
  by_contra hnot
  have hbdeg : (nearestGraph p).degree b = 6 := by
    have hle := nearestGraph_degree_le_six p hn hp b
    omega
  obtain ⟨c, _hcv, _hbc, _hwc, hsum⟩ :=
    degree_six_triangle_completion p hn hp hbdeg hwb.symm hvb.symm hvw.symm
  have hsum' : p c + p u = p w + p w := by
    calc
      p c + p u = (p v + p c) + (p u + p b) - (p v + p b) := by abel
      _ = (p b + p w) + (p v + p w) - (p v + p b) := by
        rw [hsum, hidentity]
      _ = p w + p w := by abel
  have hrel : p c - p w = -(1 : ℝ) • (p u - p w) := by
    simp only [neg_one_smul]
    calc
      p c - p w = (p c + p u) - (p w + p u) := by abel
      _ = (p w + p w) - (p w + p u) := by rw [hsum']
      _ = -(p u - p w) := by abel
  exact hull_extreme_not_opposite_ray p hp hw hwu 1 zero_lt_one hrel

end Erdos957
