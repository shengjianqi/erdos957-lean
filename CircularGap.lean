import PlanarDirections

/-!
The upper principal-argument gap between two separated points on the same
circle. Together with `equal_radius_arg_gap`, it keeps the gap in the closed
interval `[π/3, 5π/3]`.
-/

namespace Erdos957

private theorem abs_wrapped_sub_le_complement (a b : ℝ)
    (ha : a ∈ Set.Ioc (-Real.pi) Real.pi)
    (hb : b ∈ Set.Ioc (-Real.pi) Real.pi) :
    |((a - b : ℝ) : Real.Angle).toReal| ≤
      2 * Real.pi - |a - b| := by
  have hlo : -2 * Real.pi < a - b := by linarith [ha.1, hb.2]
  have hhi : a - b < 2 * Real.pi := by linarith [ha.2, hb.1]
  by_cases hleft : -Real.pi < a - b
  · by_cases hright : a - b ≤ Real.pi
    · rw [Real.Angle.toReal_coe_eq_self_iff.mpr ⟨hleft, hright⟩]
      rcases le_total b a with hba | hab
      · rw [abs_of_nonneg (by linarith : 0 ≤ a - b)]
        linarith [Real.pi_pos]
      · rw [abs_of_nonpos (by linarith : a - b ≤ 0)]
        linarith [Real.pi_pos]
    · have hright' : Real.pi < a - b := lt_of_not_ge hright
      rw [Real.Angle.toReal_coe_eq_self_sub_two_pi_iff.mpr
        (show a - b ∈ Set.Ioc Real.pi (3 * Real.pi) by
          constructor <;> linarith [Real.pi_pos])]
      rw [abs_of_nonpos (by linarith), abs_of_pos (by linarith)]
      linarith
  · have hleft' : a - b ≤ -Real.pi := le_of_not_gt hleft
    rw [Real.Angle.toReal_coe_eq_self_add_two_pi_iff.mpr
      (show a - b ∈ Set.Ioc (-3 * Real.pi) (-Real.pi) by
        constructor <;> linarith [Real.pi_pos])]
    rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
    linarith

/-- The ordinary angle between nonzero complex numbers is bounded by the
complement of the absolute difference of their principal arguments. -/
theorem complex_angle_le_arg_gap_complement {z w : ℂ}
    (hz : z ≠ 0) (hw : w ≠ 0) :
    InnerProductGeometry.angle z w ≤
      2 * Real.pi - |z.arg - w.arg| := by
  rw [Complex.angle_eq_abs_arg hz hw]
  have harg : (z / w).arg =
      ((z.arg - w.arg : ℝ) : Real.Angle).toReal := by
    apply (Complex.arg_coe_angle_eq_iff_eq_toReal).mp
    simpa only [Real.Angle.coe_sub] using (Complex.arg_div_coe_angle hz hw)
  rw [harg]
  exact abs_wrapped_sub_le_complement z.arg w.arg
    (Complex.arg_mem_Ioc z) (Complex.arg_mem_Ioc w)

/-- The principal direction parameters of two equal-radius points separated
by at least that radius cannot differ by more than `5π/3`. -/
theorem equal_radius_arg_gap_le_five_pi_div_three
    (x y z : Point) (r : ℝ) (hr : 0 < r)
    (hxy : dist x y = r) (hxz : dist x z = r)
    (hyz : r ≤ dist y z) :
    |directionArg x y - directionArg x z| ≤ 5 * Real.pi / 3 := by
  have hxy_ne : x - y ≠ 0 := by
    intro h
    have hzero : dist x y = 0 := by simp [dist_eq_norm, h]
    linarith
  have hxz_ne : x - z ≠ 0 := by
    intro h
    have hzero : dist x z = 0 := by simp [dist_eq_norm, h]
    linarith
  have hv : pointToComplex (x - y) ≠ 0 := by
    intro h
    exact hxy_ne (pointToComplex.injective (by simpa using h))
  have hw : pointToComplex (x - z) ≠ 0 := by
    intro h
    exact hxz_ne (pointToComplex.injective (by simpa using h))
  have hlower : Real.pi / 3 ≤
      InnerProductGeometry.angle (pointToComplex (x - y))
        (pointToComplex (x - z)) := by
    calc
      Real.pi / 3 ≤ InnerProductGeometry.angle (x - y) (x - z) :=
        equal_radius_angle_ge_pi_div_three x y z r hr hxy hxz hyz
      _ = InnerProductGeometry.angle (pointToComplex (x - y))
          (pointToComplex (x - z)) := by
        exact (pointToComplex.toLinearIsometry.angle_map (x - y) (x - z)).symm
  have hupper := complex_angle_le_arg_gap_complement hv hw
  change InnerProductGeometry.angle (pointToComplex (x - y))
      (pointToComplex (x - z)) ≤
      2 * Real.pi - |directionArg x y - directionArg x z| at hupper
  linarith

end Erdos957
