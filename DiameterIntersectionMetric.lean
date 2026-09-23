import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Analysis.Convex.StrictConvexBetween
import Mathlib.Tactic.Linarith

/-!
Metric transfer of intersection between pairings of four diameter endpoints.
This step uses strict convexity of a real inner product space, but no
two-dimensional topology or planar ordering.
-/

namespace Erdos957

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- If two pairs `a,b` and `c,d` are both diameter pairs of length `D`,
the cross-pairing `a,c` and `b,d` cannot intersect without the original
diameter segments also meeting at the same point. -/
theorem diameter_intersection_of_cross_intersection
    (a b c d x : E) (D : ℝ)
    (hab : dist a b = D)
    (hcd : dist c d = D)
    (hac : dist a c ≤ D)
    (hbd : dist b d ≤ D)
    (hx_ac : x ∈ segment ℝ a c)
    (hx_bd : x ∈ segment ℝ b d) :
    x ∈ segment ℝ a b ∧ x ∈ segment ℝ c d := by
  have hac_eq : dist a x + dist x c = dist a c :=
    dist_add_dist_eq_iff.mpr (mem_segment_iff_wbtw.mp hx_ac)
  have hbd_eq : dist b x + dist x d = dist b d :=
    dist_add_dist_eq_iff.mpr (mem_segment_iff_wbtw.mp hx_bd)
  have hab_le : dist a b ≤ dist a x + dist x b := dist_triangle a x b
  have hcd_le : dist c d ≤ dist c x + dist x d := dist_triangle c x d
  have hab_eq : dist a x + dist x b = dist a b := by
    linarith [dist_comm b x, dist_comm c x]
  have hcd_eq : dist c x + dist x d = dist c d := by
    linarith [dist_comm b x, dist_comm c x]
  constructor
  · exact mem_segment_iff_wbtw.mpr (dist_add_dist_eq_iff.mp hab_eq)
  · exact mem_segment_iff_wbtw.mpr (dist_add_dist_eq_iff.mp hcd_eq)

end Erdos957
