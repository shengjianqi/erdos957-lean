import SmallAngleProjection
import HullExteriorAngles
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-! Quantitative lower bounds for short chains of nearly parallel actual hull
edges. The reference direction need not be a shortest edge. -/

namespace Erdos957

private theorem small_arg_projection_along (b z : ℂ) (hb : b ≠ 0)
    (harg : |(z / b).arg| ≤ Real.pi / 600) :
    (99 / 100 : ℝ) * ‖z‖ ≤ ‖b‖ * (z / b).re := by
  have hbnorm : 0 < ‖b‖ := norm_pos_iff.mpr hb
  have hnorm : ‖z / b‖ * ‖b‖ = ‖z‖ := by
    rw [norm_div, div_mul_cancel₀ _ hbnorm.ne']
  have hproj := (small_arg_projection (z / b) harg).1
  calc
    (99 / 100 : ℝ) * ‖z‖ =
        ((99 / 100 : ℝ) * ‖z / b‖) * ‖b‖ := by rw [mul_assoc, hnorm]
    _ ≤ (z / b).re * ‖b‖ :=
      mul_le_mul_of_nonneg_right hproj hbnorm.le
    _ = ‖b‖ * (z / b).re := by ring

/-- Two vectors lying within `π / 600` of a common reference direction have
a sum of length at least `1.98` times their common lower length bound. -/
theorem short_two_vectors_chord (b z₁ z₂ : ℂ) (hb : b ≠ 0) (δ : ℝ)
    (h₁ : δ ≤ ‖z₁‖) (h₂ : δ ≤ ‖z₂‖)
    (ha₁ : |(z₁ / b).arg| ≤ Real.pi / 600)
    (ha₂ : |(z₂ / b).arg| ≤ Real.pi / 600) :
    (198 / 100 : ℝ) * δ ≤ ‖z₁ + z₂‖ := by
  have hbnorm : 0 < ‖b‖ := norm_pos_iff.mpr hb
  have hnorm : ‖(z₁ + z₂) / b‖ * ‖b‖ = ‖z₁ + z₂‖ := by
    rw [norm_div, div_mul_cancel₀ _ hbnorm.ne']
  have hre : ((z₁ + z₂) / b).re = (z₁ / b).re + (z₂ / b).re := by
    rw [add_div, Complex.add_re]
  have hbound : ‖b‖ * ((z₁ / b).re + (z₂ / b).re) ≤ ‖z₁ + z₂‖ := by
    rw [← hre]
    have h := mul_le_mul_of_nonneg_right
      (Complex.re_le_norm ((z₁ + z₂) / b)) hbnorm.le
    nlinarith
  have hp₁ := small_arg_projection_along b z₁ hb ha₁
  have hp₂ := small_arg_projection_along b z₂ hb ha₂
  linarith

/-- Three vectors lying within `π / 600` of a common reference direction have
a sum of length at least `2.97` times their common lower length bound. -/
theorem short_three_vectors_chord (b z₁ z₂ z₃ : ℂ) (hb : b ≠ 0) (δ : ℝ)
    (h₁ : δ ≤ ‖z₁‖) (h₂ : δ ≤ ‖z₂‖) (h₃ : δ ≤ ‖z₃‖)
    (ha₁ : |(z₁ / b).arg| ≤ Real.pi / 600)
    (ha₂ : |(z₂ / b).arg| ≤ Real.pi / 600)
    (ha₃ : |(z₃ / b).arg| ≤ Real.pi / 600) :
    (297 / 100 : ℝ) * δ ≤ ‖z₁ + z₂ + z₃‖ := by
  have hbnorm : 0 < ‖b‖ := norm_pos_iff.mpr hb
  have hnorm : ‖(z₁ + z₂ + z₃) / b‖ * ‖b‖ = ‖z₁ + z₂ + z₃‖ := by
    rw [norm_div, div_mul_cancel₀ _ hbnorm.ne']
  have hre : ((z₁ + z₂ + z₃) / b).re =
      (z₁ / b).re + (z₂ / b).re + (z₃ / b).re := by
    rw [add_div, add_div, Complex.add_re, Complex.add_re]
  have hbound : ‖b‖ * ((z₁ / b).re + (z₂ / b).re + (z₃ / b).re) ≤
      ‖z₁ + z₂ + z₃‖ := by
    rw [← hre]
    have h := mul_le_mul_of_nonneg_right
      (Complex.re_le_norm ((z₁ + z₂ + z₃) / b)) hbnorm.le
    nlinarith
  have hp₁ := small_arg_projection_along b z₁ hb ha₁
  have hp₂ := small_arg_projection_along b z₂ hb ha₂
  have hp₃ := small_arg_projection_along b z₃ hb ha₃
  linarith

private theorem hull_edge_norm_eq_dist {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (v : Fin h → Fin n) (i : Fin h) :
    ‖hullEdgeDirection p v i‖ = dist (p (v i)) (p (v (i + 1))) := by
  rw [hullEdgeDirection, pointToComplex.norm_map]
  simp only [dist_eq_norm, norm_sub_rev]

/-- Two consecutive actual hull edges form a chord of length at least
`1.98 δ` when each has length at least `δ` and both are nearly parallel. -/
theorem short_hull_two_edge_chord {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (v : Fin h → Fin n) (i : Fin h)
    (b : ℂ) (hb : b ≠ 0) (δ : ℝ)
    (h₁ : δ ≤ dist (p (v i)) (p (v (i + 1))))
    (h₂ : δ ≤ dist (p (v (i + 1))) (p (v ((i + 1) + 1))))
    (ha₁ : |(hullEdgeDirection p v i / b).arg| ≤ Real.pi / 600)
    (ha₂ : |(hullEdgeDirection p v (i + 1) / b).arg| ≤ Real.pi / 600) :
    (198 / 100 : ℝ) * δ ≤
      dist (p (v i)) (p (v ((i + 1) + 1))) := by
  let e₁ := hullEdgeDirection p v i
  let e₂ := hullEdgeDirection p v (i + 1)
  have hsum : e₁ + e₂ =
      pointToComplex (p (v ((i + 1) + 1)) - p (v i)) := by
    change pointToComplex (p (v (i + 1)) - p (v i)) +
      pointToComplex (p (v ((i + 1) + 1)) - p (v (i + 1))) = _
    rw [← map_add]
    congr 1
    abel
  have hnorm : ‖e₁ + e₂‖ =
      dist (p (v i)) (p (v ((i + 1) + 1))) := by
    rw [hsum, pointToComplex.norm_map]
    simp only [dist_eq_norm, norm_sub_rev]
  rw [← hnorm]
  exact short_two_vectors_chord b e₁ e₂ hb δ
    (by simpa only [e₁, hull_edge_norm_eq_dist] using h₁)
    (by simpa only [e₂, hull_edge_norm_eq_dist] using h₂)
    ha₁ ha₂

/-- Three consecutive actual hull edges form a chord of length at least
`2.97 δ` under the same direction and length bounds. -/
theorem short_hull_three_edge_chord {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (v : Fin h → Fin n) (i : Fin h)
    (b : ℂ) (hb : b ≠ 0) (δ : ℝ)
    (h₁ : δ ≤ dist (p (v i)) (p (v (i + 1))))
    (h₂ : δ ≤ dist (p (v (i + 1))) (p (v ((i + 1) + 1))))
    (h₃ : δ ≤ dist (p (v ((i + 1) + 1)))
      (p (v (((i + 1) + 1) + 1))))
    (ha₁ : |(hullEdgeDirection p v i / b).arg| ≤ Real.pi / 600)
    (ha₂ : |(hullEdgeDirection p v (i + 1) / b).arg| ≤ Real.pi / 600)
    (ha₃ : |(hullEdgeDirection p v ((i + 1) + 1) / b).arg| ≤ Real.pi / 600) :
    (297 / 100 : ℝ) * δ ≤
      dist (p (v i)) (p (v (((i + 1) + 1) + 1))) := by
  let e₁ := hullEdgeDirection p v i
  let e₂ := hullEdgeDirection p v (i + 1)
  let e₃ := hullEdgeDirection p v ((i + 1) + 1)
  have hsum : e₁ + e₂ + e₃ =
      pointToComplex (p (v (((i + 1) + 1) + 1)) - p (v i)) := by
    change pointToComplex (p (v (i + 1)) - p (v i)) +
      pointToComplex (p (v ((i + 1) + 1)) - p (v (i + 1))) +
      pointToComplex (p (v (((i + 1) + 1) + 1)) - p (v ((i + 1) + 1))) = _
    rw [← map_add, ← map_add]
    congr 1
    abel
  have hnorm : ‖e₁ + e₂ + e₃‖ =
      dist (p (v i)) (p (v (((i + 1) + 1) + 1))) := by
    rw [hsum, pointToComplex.norm_map]
    simp only [dist_eq_norm, norm_sub_rev]
  rw [← hnorm]
  exact short_three_vectors_chord b e₁ e₂ e₃ hb δ
    (by simpa only [e₁, hull_edge_norm_eq_dist] using h₁)
    (by simpa only [e₂, hull_edge_norm_eq_dist] using h₂)
    (by simpa only [e₃, hull_edge_norm_eq_dist] using h₃)
    ha₁ ha₂ ha₃

end Erdos957
