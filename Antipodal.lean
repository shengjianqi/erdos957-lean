import PlanarDirections
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
Opposite principal directions on a circle yield antipodal points.
-/

namespace Erdos957

private theorem abs_wrapped_eq_pi_of_abs_eq_pi (t : ℝ)
    (ht : |t| = Real.pi) : |(t : Real.Angle).toReal| = Real.pi := by
  rcases le_total 0 t with hnonneg | hnonpos
  · have heq : t = Real.pi := by simpa [abs_of_nonneg hnonneg] using ht
    rw [heq, Real.Angle.toReal_coe_eq_self_iff.mpr
      ⟨by linarith [Real.pi_pos], le_rfl⟩]
    exact abs_of_pos Real.pi_pos
  · have heq : t = -Real.pi := by
      have h := ht
      rw [abs_of_nonpos hnonpos] at h
      linarith
    rw [heq, Real.Angle.toReal_coe_eq_self_add_two_pi_iff.mpr
      (show -Real.pi ∈ Set.Ioc (-3 * Real.pi) (-Real.pi) by
        constructor <;> linarith [Real.pi_pos])]
    have hpi : -Real.pi + 2 * Real.pi = Real.pi := by ring
    rw [hpi]
    exact abs_of_pos Real.pi_pos

private theorem complex_angle_eq_pi_of_arg_gap_eq_pi {u v : ℂ}
    (hu : u ≠ 0) (hv : v ≠ 0)
    (hgap : |u.arg - v.arg| = Real.pi) :
    InnerProductGeometry.angle u v = Real.pi := by
  rw [Complex.angle_eq_abs_arg hu hv]
  have harg : (u / v).arg =
      ((u.arg - v.arg : ℝ) : Real.Angle).toReal := by
    apply (Complex.arg_coe_angle_eq_iff_eq_toReal).mp
    simpa only [Real.Angle.coe_sub] using (Complex.arg_div_coe_angle hu hv)
  rw [harg]
  exact abs_wrapped_eq_pi_of_abs_eq_pi _ hgap

/-- Two points on the same circle whose principal direction arguments differ
by `π` are antipodal about the center. -/
theorem equal_radius_arg_gap_pi_antipodal
    (x y z : Point) (r : ℝ) (hr : 0 < r)
    (hxy : dist x y = r) (hxz : dist x z = r)
    (hgap : |directionArg x y - directionArg x z| = Real.pi) :
    y + z = 2 • x := by
  have hxy_ne : x - y ≠ 0 := by
    intro h
    have hzero : dist x y = 0 := by simp [dist_eq_norm, h]
    linarith
  have hxz_ne : x - z ≠ 0 := by
    intro h
    have hzero : dist x z = 0 := by simp [dist_eq_norm, h]
    linarith
  have hu : pointToComplex (x - y) ≠ 0 := by
    intro h
    exact hxy_ne (pointToComplex.injective (by simpa using h))
  have hv : pointToComplex (x - z) ≠ 0 := by
    intro h
    exact hxz_ne (pointToComplex.injective (by simpa using h))
  have hangle : InnerProductGeometry.angle (x - y) (x - z) = Real.pi := by
    calc
      InnerProductGeometry.angle (x - y) (x - z) =
          InnerProductGeometry.angle (pointToComplex (x - y))
            (pointToComplex (x - z)) :=
            (pointToComplex.toLinearIsometry.angle_map (x - y) (x - z)).symm
      _ = Real.pi := complex_angle_eq_pi_of_arg_gap_eq_pi hu hv hgap
  obtain ⟨_, t, ht, hvec⟩ := InnerProductGeometry.angle_eq_pi_iff.mp hangle
  have hnormxy : ‖x - y‖ = r := by simpa only [dist_eq_norm] using hxy
  have hnormxz : ‖x - z‖ = r := by simpa only [dist_eq_norm] using hxz
  have htneg : |t| = -t := abs_of_neg ht
  have htval : t = -1 := by
    have hnorm : ‖x - z‖ = |t| * ‖x - y‖ := by rw [hvec, norm_smul, Real.norm_eq_abs]
    rw [hnormxy, hnormxz, htneg] at hnorm
    nlinarith
  have hvec' : x - z = -(x - y) := by simpa [htval] using hvec
  have hsum : y + z = x + x := by
    calc
      y + z = y + z + ((x - z) + (x - y)) := by rw [hvec']; abel
      _ = x + x := by abel
  simpa [two_smul] using hsum

end Erdos957
