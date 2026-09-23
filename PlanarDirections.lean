import Foundations
import Geometry
import Mathlib.Analysis.Complex.Angle
import Mathlib.Tactic.Linarith

/-!
Direction parameters for the Euclidean plane.  We use the complex argument in
`(-π, π]`; a 60-degree lower bound on the ordinary angle implies the same
lower bound on the absolute difference of these real parameters.
-/

namespace Erdos957

/-- The standard real-linear isometry from the Euclidean plane to `ℂ`. -/
noncomputable abbrev pointToComplex : Point ≃ₗᵢ[ℝ] ℂ :=
  Complex.orthonormalBasisOneI.repr.symm

private theorem abs_wrapped_sub_le_abs (a b : ℝ)
    (ha : a ∈ Set.Ioc (-Real.pi) Real.pi)
    (hb : b ∈ Set.Ioc (-Real.pi) Real.pi) :
    |((a - b : ℝ) : Real.Angle).toReal| ≤ |a - b| := by
  have hlo : -2 * Real.pi < a - b := by linarith [ha.1, hb.2]
  have hhi : a - b < 2 * Real.pi := by linarith [ha.2, hb.1]
  by_cases hleft : -Real.pi < a - b
  · by_cases hright : a - b ≤ Real.pi
    · rw [Real.Angle.toReal_coe_eq_self_iff.mpr ⟨hleft, hright⟩]
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

/-- The ordinary Euclidean angle between two nonzero complex numbers is at
most the absolute difference of their principal arguments. -/
theorem complex_angle_le_arg_gap {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0) :
    InnerProductGeometry.angle z w ≤ |z.arg - w.arg| := by
  rw [Complex.angle_eq_abs_arg hz hw]
  have harg : (z / w).arg =
      ((z.arg - w.arg : ℝ) : Real.Angle).toReal := by
    apply (Complex.arg_coe_angle_eq_iff_eq_toReal).mp
    simpa only [Real.Angle.coe_sub] using (Complex.arg_div_coe_angle hz hw)
  rw [harg]
  exact abs_wrapped_sub_le_abs z.arg w.arg (Complex.arg_mem_Ioc z)
    (Complex.arg_mem_Ioc w)

/-- Equal-radius plane neighbors separated by at least their common radius
have principal direction parameters at least `π / 3` apart. -/
theorem equal_radius_arg_gap
    (x y z : Point) (r : ℝ) (hr : 0 < r)
    (hxy : dist x y = r) (hxz : dist x z = r)
    (hyz : r ≤ dist y z) :
    Real.pi / 3 ≤
      |(pointToComplex (x - y)).arg - (pointToComplex (x - z)).arg| := by
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
  calc
    Real.pi / 3 ≤ InnerProductGeometry.angle (x - y) (x - z) :=
      equal_radius_angle_ge_pi_div_three x y z r hr hxy hxz hyz
    _ = InnerProductGeometry.angle (pointToComplex (x - y))
        (pointToComplex (x - z)) := by
          exact (pointToComplex.toLinearIsometry.angle_map (x - y) (x - z)).symm
    _ ≤ |(pointToComplex (x - y)).arg - (pointToComplex (x - z)).arg| :=
      complex_angle_le_arg_gap hv hw

/-- The principal argument of `x - y`, used as a consistent direction
parameter. This is the direction from `y` toward `x`; `halfplaneArg` instead
uses the outward vector `y - x` in a rotated coordinate system. -/
noncomputable def directionArg (x y : Point) : ℝ :=
  (pointToComplex (x - y)).arg

theorem directionArg_mem_Ioc (x y : Point) :
    directionArg x y ∈ Set.Ioc (-Real.pi) Real.pi :=
  Complex.arg_mem_Ioc _

/-- Direction parameters of distinct nearest neighbors are separated by at
least `π / 3` on the real interval `(-π, π]`. -/
theorem neighbor_directionArg_separated
    (N : Finset Point) (x : Point) (r : ℝ) (hr : 0 < r)
    (hradius : ∀ y ∈ N, dist x y = r)
    (hsep : ∀ y ∈ N, ∀ z ∈ N, y ≠ z → r ≤ dist y z)
    {y z : Point} (hy : y ∈ N) (hz : z ∈ N) (hyz : y ≠ z) :
    Real.pi / 3 ≤ |directionArg x y - directionArg x z| :=
  equal_radius_arg_gap x y z r hr (hradius y hy) (hradius z hz)
    (hsep y hy z hz hyz)

/-- The direction parameter is injective on any set of nearest neighbors. -/
theorem neighbor_directionArg_injOn
    (N : Finset Point) (x : Point) (r : ℝ) (hr : 0 < r)
    (hradius : ∀ y ∈ N, dist x y = r)
    (hsep : ∀ y ∈ N, ∀ z ∈ N, y ≠ z → r ≤ dist y z) :
    Set.InjOn (directionArg x) (N : Set Point) := by
  intro y hy z hz heq
  by_contra hne
  have hgap := neighbor_directionArg_separated N x r hr hradius hsep hy hz hne
  rw [heq, sub_self, abs_zero] at hgap
  linarith [Real.pi_pos]

end Erdos957
