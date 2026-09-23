import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Analysis.Convex.StrictConvexBetween
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
Four-point rigidity toward the fact that independent diameter edges cross in
the Euclidean plane. The full crossing statement also needs planar order; this
file isolates the metric obstruction to two translated parallel diameter
edges.
-/

namespace Erdos957

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- If both `u + w` and `u - w` are no longer than `u`, then `w = 0`.
This is the rigidity case of the parallelogram law. -/
theorem parallelogram_rigidity (u w : E)
    (hplus : ‖u + w‖ ≤ ‖u‖)
    (hminus : ‖u - w‖ ≤ ‖u‖) : w = 0 := by
  have hp : ‖u + w‖ ^ 2 ≤ ‖u‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hplus
  have hm : ‖u - w‖ ^ 2 ≤ ‖u‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hminus
  have hpar := parallelogram_law_with_norm ℝ u w
  have hw : ‖w‖ = 0 := by
    nlinarith [sq_nonneg ‖w‖, norm_nonneg w]
  exact norm_eq_zero.mp hw

/-- Two equal directed segments cannot be distinct diameter edges: if all
cross-distances are no greater than their common length, the segments coincide.
Only two of the four cross-distance bounds are needed. -/
theorem equal_directed_diameters_coincide (a b c d : E)
    (hvec : b - a = d - c)
    (had : dist a d ≤ dist a b)
    (hbc : dist b c ≤ dist a b) :
    a = c ∧ b = d := by
  let u : E := b - a
  let w : E := c - a
  have hd : d - a = u + w := by
    calc
      d - a = (d - c) + (c - a) := by abel
      _ = u + w := by rw [← hvec]
  have hbcvec : b - c = u - w := by
    dsimp [u, w]
    abel
  have hplus : ‖u + w‖ ≤ ‖u‖ := by
    rw [← hd]
    change ‖d - a‖ ≤ ‖b - a‖
    simpa only [dist_eq_norm] using
      (show dist d a ≤ dist b a by
        calc
          dist d a = dist a d := dist_comm _ _
          _ ≤ dist a b := had
          _ = dist b a := dist_comm _ _)
  have hminus : ‖u - w‖ ≤ ‖u‖ := by
    rw [← hbcvec]
    change ‖b - c‖ ≤ ‖b - a‖
    simpa only [dist_eq_norm] using
      (show dist b c ≤ dist b a by
        calc
          dist b c ≤ dist a b := hbc
          _ = dist b a := dist_comm _ _)
  have hw : w = 0 := parallelogram_rigidity u w hplus hminus
  have hac : a = c := by
    have hca : c = a := sub_eq_zero.mp hw
    exact hca.symm
  constructor
  · exact hac
  · have hsame : b - a = d - a := by simpa [← hac] using hvec
    exact sub_left_inj.mp hsame

/-- Distinct translated copies of one segment cannot both be diameter edges:
at least one cross-distance exceeds the segment length. -/
theorem translated_segments_have_long_cross_distance (a b c d : E)
    (hvec : b - a = d - c) (hac : a ≠ c) :
    dist a b < dist a d ∨ dist a b < dist b c := by
  by_contra h
  push Not at h
  exact hac (equal_directed_diameters_coincide a b c d hvec h.1 h.2).1

/-- The same rigidity holds when the second segment is oriented oppositely. -/
theorem opposite_directed_diameters_coincide (a b c d : E)
    (hvec : b - a = c - d)
    (hac : dist a c ≤ dist a b)
    (hbd : dist b d ≤ dist a b) :
    a = d ∧ b = c :=
  equal_directed_diameters_coincide a b d c hvec hac hbd

/-- If the opposite pairing of four points crosses at `x`, the triangle
inequality bounds the sum of the other pairing by the lengths of the crossing
segments. One noncollinear triangle makes the bound strict. -/
theorem sum_of_opposite_sides_lt_crossing_diagonals
    (a b c d x : E)
    (hx_ac : x ∈ segment ℝ a c)
    (hx_bd : x ∈ segment ℝ b d)
    (hstrict : dist a b < dist a x + dist x b) :
    dist a b + dist c d < dist a c + dist b d := by
  have hac : dist a x + dist x c = dist a c :=
    dist_add_dist_eq_iff.mpr (mem_segment_iff_wbtw.mp hx_ac)
  have hbd : dist b x + dist x d = dist b d :=
    dist_add_dist_eq_iff.mpr (mem_segment_iff_wbtw.mp hx_bd)
  have hcd : dist c d ≤ dist c x + dist x d := dist_triangle c x d
  linarith [dist_comm x b, dist_comm c x]

end Erdos957
