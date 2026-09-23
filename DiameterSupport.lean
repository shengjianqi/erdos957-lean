import Geometry

/-! Strict supporting inequalities at a farthest point in a real inner product space. -/

namespace Erdos957

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every point no farther from `b` than `a` lies on the inner side of the
supporting hyperplane at `a`, with a quantitative squared-distance margin. -/
theorem farthest_inner_margin (a b z : E) (hz : dist b z ≤ dist b a) :
    2 * inner ℝ (a - b) (z - a) + ‖z - a‖ ^ 2 ≤ 0 := by
  have hnorm : ‖z - b‖ ≤ ‖a - b‖ := by
    simpa only [dist_eq_norm, norm_sub_rev] using hz
  have hsq : ‖z - b‖ ^ 2 ≤ ‖a - b‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hnorm
  have hexpand := norm_add_sq_real (a - b) (z - a)
  have hsum : (a - b) + (z - a) = z - b := by abel
  rw [hsum] at hexpand
  linarith

/-- The supporting inequality is strict away from the farthest point. -/
theorem farthest_inner_strict (a b z : E)
    (hz : dist b z ≤ dist b a) (hza : z ≠ a) :
    inner ℝ (a - b) (z - a) < 0 := by
  have hmargin := farthest_inner_margin a b z hz
  have hpositive : 0 < ‖z - a‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hza))
  linarith

/-- A farthest point uniquely maximizes the linear functional in its radial
direction over every set contained in the corresponding closed ball. -/
theorem farthest_support_strict (a b z : E)
    (hz : dist b z ≤ dist b a) (hza : z ≠ a) :
    inner ℝ (a - b) z < inner ℝ (a - b) a := by
  have hstrict := farthest_inner_strict a b z hz hza
  rw [inner_sub_right] at hstrict
  linarith

end Erdos957
