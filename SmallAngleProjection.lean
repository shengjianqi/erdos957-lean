import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.Arg
import Mathlib.Tactic.Linarith

/-! Projection bounds for vectors whose principal direction differs from the
positive real axis by at most `π / 600`. -/

namespace Erdos957

private theorem small_arg_trigonometric_bounds (θ : ℝ)
    (hθ : |θ| ≤ Real.pi / 600) :
    (99 / 100 : ℝ) ≤ Real.cos θ ∧
      |Real.sin θ| ≤ Real.cos θ / 30 := by
  have hπ : Real.pi / 600 ≤ (1 / 150 : ℝ) := by
    have h := Real.pi_le_four
    linarith
  have hbound : |θ| ≤ (1 / 150 : ℝ) := hθ.trans hπ
  have hupper : θ ≤ (1 / 150 : ℝ) := (le_abs_self θ).trans hbound
  have hlower : -(1 / 150 : ℝ) ≤ θ := by
    have h := neg_le_of_abs_le hbound
    linarith
  have hprod : 0 ≤ ((1 / 150 : ℝ) - θ) * ((1 / 150 : ℝ) + θ) :=
    mul_nonneg (by linarith) (by linarith)
  have hsq : θ ^ 2 ≤ (1 / 150 : ℝ) ^ 2 := by nlinarith
  have hcos0 := Real.one_sub_sq_div_two_le_cos (x := θ)
  have hcos : (99 / 100 : ℝ) ≤ Real.cos θ := by nlinarith
  have hsin : |Real.sin θ| ≤ (1 / 150 : ℝ) :=
    (Real.abs_sin_le_abs).trans hbound
  constructor
  · exact hcos
  · linarith

/-- A vector within `π / 600` of the positive real axis projects almost all
of its length horizontally and has vertical slope at most `1 / 30`. -/
theorem small_arg_projection (z : ℂ)
    (harg : |z.arg| ≤ Real.pi / 600) :
    (99 / 100 : ℝ) * ‖z‖ ≤ z.re ∧ |z.im| ≤ z.re / 30 := by
  obtain ⟨hcos, hsin⟩ := small_arg_trigonometric_bounds z.arg harg
  have hre : z.re = ‖z‖ * Real.cos z.arg :=
    (Complex.norm_mul_cos_arg z).symm
  have him : z.im = ‖z‖ * Real.sin z.arg :=
    (Complex.norm_mul_sin_arg z).symm
  have hnorm : 0 ≤ ‖z‖ := norm_nonneg z
  constructor
  · rw [hre]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hcos hnorm
  · rw [him, hre, abs_mul, abs_of_nonneg hnorm]
    have h := mul_le_mul_of_nonneg_left hsin hnorm
    nlinarith

/-- The horizontal projection of a short-angle vector of length at least one
is at least `99 / 100`, hence strictly positive. -/
theorem small_arg_unit_projection (z : ℂ)
    (harg : |z.arg| ≤ Real.pi / 600) (hnorm : 1 ≤ ‖z‖) :
    (99 / 100 : ℝ) ≤ z.re ∧ 0 < z.re := by
  have h := (small_arg_projection z harg).1
  constructor <;> nlinarith

end Erdos957
