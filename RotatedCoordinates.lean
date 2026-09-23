import HalfplanePacking
import RadialAngles
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Module

/-! Coordinates rotated by the conjugate of a chosen nonzero axis. -/

namespace Erdos957

open scoped ComplexConjugate

/-- The unnormalized complex coordinates based at `x`, with the positive real
axis pointing along `axis`. -/
noncomputable def rotatedCoordinate (x axis y : Point) : ℂ :=
  conj (pointToComplex axis) * pointToComplex (y - x)

theorem rotatedCoordinate_arg (x axis y : Point) :
    (rotatedCoordinate x axis y).arg = halfplaneArg x axis y := rfl

theorem rotatedCoordinate_norm (x axis y : Point) :
    ‖rotatedCoordinate x axis y‖ = ‖axis‖ * dist x y := by
  rw [rotatedCoordinate, norm_mul, Complex.norm_conj, pointToComplex.norm_map,
    pointToComplex.norm_map, dist_eq_norm, norm_sub_rev]

theorem rotatedCoordinate_norm_of_dist (x axis y : Point) (r : ℝ)
    (hxy : dist x y = r) :
    ‖rotatedCoordinate x axis y‖ = ‖axis‖ * r := by
  rw [rotatedCoordinate_norm, hxy]

theorem rotatedCoordinate_re (x axis y : Point) :
    (rotatedCoordinate x axis y).re =
      (‖axis‖ * dist x y) * Real.cos (halfplaneArg x axis y) := by
  rw [← rotatedCoordinate_arg, ← rotatedCoordinate_norm]
  exact (Complex.norm_mul_cos_arg _).symm

theorem rotatedCoordinate_im (x axis y : Point) :
    (rotatedCoordinate x axis y).im =
      (‖axis‖ * dist x y) * Real.sin (halfplaneArg x axis y) := by
  rw [← rotatedCoordinate_arg, ← rotatedCoordinate_norm]
  exact (Complex.norm_mul_sin_arg _).symm

theorem rotatedCoordinate_re_of_dist (x axis y : Point) (r : ℝ)
    (hxy : dist x y = r) :
    (rotatedCoordinate x axis y).re =
      (‖axis‖ * r) * Real.cos (halfplaneArg x axis y) := by
  rw [rotatedCoordinate_re, hxy]

theorem rotatedCoordinate_im_of_dist (x axis y : Point) (r : ℝ)
    (hxy : dist x y = r) :
    (rotatedCoordinate x axis y).im =
      (‖axis‖ * r) * Real.sin (halfplaneArg x axis y) := by
  rw [rotatedCoordinate_im, hxy]

/-- The axis endpoint is mapped to the positive real scalar `‖axis‖²`. -/
theorem rotatedCoordinate_axis (x axis : Point) :
    rotatedCoordinate x axis (x + axis) = ((‖axis‖ ^ 2 : ℝ) : ℂ) := by
  simp only [rotatedCoordinate, add_sub_cancel_left]
  calc
    conj (pointToComplex axis) * pointToComplex axis =
        (Complex.normSq (pointToComplex axis) : ℂ) :=
      Complex.normSq_eq_conj_mul_self.symm
    _ = ((‖pointToComplex axis‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.normSq_eq_norm_sq]
    _ = ((‖axis‖ ^ 2 : ℝ) : ℂ) := by
      rw [pointToComplex.norm_map]

theorem rotatedCoordinate_sub (x axis a b : Point) :
    rotatedCoordinate x axis b - rotatedCoordinate x axis a =
      conj (pointToComplex axis) * pointToComplex (b - a) := by
  simp only [rotatedCoordinate, ← mul_sub, ← map_sub,
    sub_sub_sub_cancel_right]

/-- Rotated complex signed area is the original signed area scaled by the
squared norm of the axis. -/
theorem rotatedCoordinate_turn (x axis a b c : Point) :
    (conj (rotatedCoordinate x axis b - rotatedCoordinate x axis a) *
      (rotatedCoordinate x axis c - rotatedCoordinate x axis a)).im =
      ‖axis‖ ^ 2 * turn a b c := by
  rw [rotatedCoordinate_sub, rotatedCoordinate_sub]
  let A := pointToComplex axis
  let u := pointToComplex (b - a)
  let v := pointToComplex (c - a)
  have hcomplex : conj (conj A * u) * (conj A * v) =
      (Complex.normSq A : ℂ) * (conj u * v) := by
    simp only [map_mul, Complex.conj_conj]
    rw [Complex.normSq_eq_conj_mul_self]
    ring
  rw [hcomplex]
  simp only [Complex.im_ofReal_mul, Complex.normSq_eq_norm_sq]
  change ‖pointToComplex axis‖ ^ 2 *
      (conj (pointToComplex (b - a)) * pointToComplex (c - a)).im = _
  rw [pointToComplex.norm_map]
  exact congrArg (fun q : ℝ => ‖axis‖ ^ 2 * q)
    (turn_eq_im_conj_mul a b c).symm

/-- For a nonzero axis, the rotated complex determinant has the same strict
sign as the original planar signed turn. -/
theorem rotatedCoordinate_turn_pos_iff (x axis a b c : Point)
    (haxis : axis ≠ 0) :
    0 < (conj (rotatedCoordinate x axis b - rotatedCoordinate x axis a) *
      (rotatedCoordinate x axis c - rotatedCoordinate x axis a)).im ↔
      0 < turn a b c := by
  rw [rotatedCoordinate_turn]
  have hnorm : 0 < ‖axis‖ := norm_pos_iff.mpr haxis
  exact mul_pos_iff_of_pos_left (sq_pos_of_pos hnorm)

end Erdos957
