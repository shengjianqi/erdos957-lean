import Geometry

/-! Diameter axes at close endpoints point in compatible directions. -/

namespace Erdos957

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- If two diameter endpoints are less than one third of a diameter apart,
the vectors toward any two corresponding diameter partners have positive
inner product. This metric fact is valid in any real inner product space. -/
theorem diameter_axes_inner_pos_of_three_mul_dist_lt
    (u w j k : E) (D : ℝ)
    (huj : dist u j = D) (hwk : dist w k = D)
    (hjk : dist j k ≤ D) (hlong : 3 * dist u w < D) :
    0 < inner ℝ (j - u) (k - w) := by
  have hr : 0 ≤ dist u w := dist_nonneg
  have hD : 0 < D := by linarith
  have hA : ‖j - u‖ = D := by
    simpa only [dist_eq_norm, norm_sub_rev] using huj
  have hB : ‖k - w‖ = D := by
    simpa only [dist_eq_norm, norm_sub_rev] using hwk
  have hdiff : (j - u) - (k - w) = (j - k) + (w - u) := by abel
  have hbound : ‖(j - u) - (k - w)‖ ≤ D + dist u w := by
    rw [hdiff]
    calc
      ‖(j - k) + (w - u)‖ ≤ ‖j - k‖ + ‖w - u‖ := norm_add_le _ _
      _ ≤ D + dist u w := by
        simpa only [dist_eq_norm, norm_sub_rev, add_comm] using
          add_le_add_right hjk (dist u w)
  have hsq : ‖(j - u) - (k - w)‖ ^ 2 ≤ (D + dist u w) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hbound
  have hexpand := norm_sub_sq_real (j - u) (k - w)
  rw [hA, hB] at hexpand
  have hprod : 0 < (D - 3 * dist u w) * (D + dist u w) :=
    mul_pos (by linarith) (by positivity)
  by_contra hnot
  have hnonpos := le_of_not_gt hnot
  nlinarith [sq_nonneg (dist u w)]

end Erdos957
