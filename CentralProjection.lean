import RotatedCoordinates

/-! The central nearest direction has strictly maximal inward projection. -/

namespace Erdos957

open scoped ComplexConjugate

theorem rotatedCoordinate_re_eq_inner (x axis y : Point) :
    (rotatedCoordinate x axis y).re = inner ℝ axis (y - x) := by
  calc
    (rotatedCoordinate x axis y).re =
        inner ℝ (pointToComplex axis) (pointToComplex (y - x)) := by
      rw [Complex.inner, mul_comm]
      rfl
    _ = inner ℝ axis (y - x) :=
      pointToComplex.toLinearIsometry.inner_map_map axis (y - x)

/-- In the strict inward semicircle, a direction within thirty degrees of
the axis has greater axial projection than any equal-radius point separated
from it by at least that radius. -/
theorem central_neighbor_inner_gt (x axis v a : Point) (r : ℝ)
    (hr : 0 < r) (hv : dist x v = r) (ha : dist x a = r)
    (hsep : r ≤ dist v a)
    (hvhalf : 0 < inner ℝ axis (v - x))
    (hahalf : 0 < inner ℝ axis (a - x))
    (hvlo : -Real.pi / 6 < halfplaneArg x axis v)
    (hvhi : halfplaneArg x axis v < Real.pi / 6) :
    inner ℝ axis (a - x) < inner ℝ axis (v - x) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  let α := halfplaneArg x axis a
  let β := halfplaneArg x axis v
  have hβabs : |β| < Real.pi / 6 := abs_lt.mpr ⟨by linarith, hvhi⟩
  have hαbounds := halfplaneArg_mem_Ioo hahalf
  have hαabs : |α| < Real.pi / 2 := abs_lt.mpr ⟨by linarith [hαbounds.1], hαbounds.2⟩
  have hgap : Real.pi / 3 ≤ |β - α| :=
    halfplaneArg_gap x axis v a r hr hv ha hsep hvhalf
  have habs : |β| < |α| := by
    by_contra h
    have hle : |α| ≤ |β| := le_of_not_gt h
    have htriangle := abs_sub_le β 0 α
    simp only [sub_zero, zero_sub, abs_neg] at htriangle
    linarith
  have hcos : Real.cos α < Real.cos β := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg β)
      (show |α| ≤ Real.pi by linarith) habs
    simpa only [Real.cos_abs] using h
  have haxis : axis ≠ 0 := by
    intro h
    simp only [h, inner_zero_left] at hvhalf
    linarith
  have hscale : 0 < ‖axis‖ * r := mul_pos (norm_pos_iff.mpr haxis) hr
  rw [← rotatedCoordinate_re_eq_inner x axis a,
    ← rotatedCoordinate_re_eq_inner x axis v,
    rotatedCoordinate_re_of_dist x axis a r ha,
    rotatedCoordinate_re_of_dist x axis v r hv]
  exact mul_lt_mul_of_pos_left hcos hscale

end Erdos957
