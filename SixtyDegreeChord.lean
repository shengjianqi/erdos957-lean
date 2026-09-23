import PlanarDirections
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Equal-radius chords for adjacent directions of a regular hexagon. -/

namespace Erdos957

open scoped ComplexConjugate

private theorem cos_of_sixty_or_wrap {t : ℝ}
    (ht : |t| = Real.pi / 3 ∨ |t| = 5 * Real.pi / 3) :
    Real.cos t = 1 / 2 := by
  rw [← Real.cos_abs]
  rcases ht with ht | ht
  · rw [ht, Real.cos_pi_div_three]
  · have heq : 5 * Real.pi / 3 = 2 * Real.pi - Real.pi / 3 := by ring
    rw [ht, heq, Real.cos_two_pi_sub, Real.cos_pi_div_three]

private theorem complex_re_mul_conj_eq_cos_arg_gap (z w : ℂ) :
    (z * conj w).re = ‖z‖ * ‖w‖ * Real.cos (z.arg - w.arg) := by
  have hzre := Complex.norm_mul_cos_arg z
  have hwre := Complex.norm_mul_cos_arg w
  have hzim := Complex.norm_mul_sin_arg z
  have hwim := Complex.norm_mul_sin_arg w
  calc
    (z * conj w).re = z.re * w.re + z.im * w.im := by
      simp [Complex.mul_re]
    _ = ‖z‖ * ‖w‖ *
        (Real.cos z.arg * Real.cos w.arg + Real.sin z.arg * Real.sin w.arg) := by
      rw [← hzre, ← hwre, ← hzim, ← hwim]
      ring
    _ = ‖z‖ * ‖w‖ * Real.cos (z.arg - w.arg) := by rw [Real.cos_sub]

/-- Two complex vectors of the same positive radius, with principal arguments
separated by `π/3` or `5π/3`, have a chord of that radius. The second case
accounts for the cut in the principal argument at `π`. -/
theorem complex_dist_eq_radius_of_arg_gap (z w : ℂ) (r : ℝ) (hr : 0 < r)
    (hz : ‖z‖ = r) (hw : ‖w‖ = r)
    (hgap : |z.arg - w.arg| = Real.pi / 3 ∨
      |z.arg - w.arg| = 5 * Real.pi / 3) :
    dist z w = r := by
  have hcos := cos_of_sixty_or_wrap hgap
  have hmul := complex_re_mul_conj_eq_cos_arg_gap z w
  have hsq : ‖z - w‖ ^ 2 = r ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub,
      Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, hmul, hz, hw, hcos]
    ring
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (z - w)]

/-- A sixty-degree step between two rays from the same point has chord length
equal to their common radius, including the wrap across the argument cut. -/
theorem dist_eq_radius_of_directionArg_gap
    (x y z : Point) (r : ℝ) (hr : 0 < r)
    (hxy : dist x y = r) (hxz : dist x z = r)
    (hgap : |directionArg x y - directionArg x z| = Real.pi / 3 ∨
      |directionArg x y - directionArg x z| = 5 * Real.pi / 3) :
    dist y z = r := by
  let u : ℂ := pointToComplex (x - y)
  let v : ℂ := pointToComplex (x - z)
  have hu : ‖u‖ = r := by
    simpa only [u, pointToComplex.norm_map, dist_eq_norm, norm_sub_rev] using hxy
  have hv : ‖v‖ = r := by
    simpa only [v, pointToComplex.norm_map, dist_eq_norm, norm_sub_rev] using hxz
  have hdist := complex_dist_eq_radius_of_arg_gap u v r hr hu hv hgap
  have hvec : (x - y) - (x - z) = z - y := by abel
  calc
    dist y z = ‖z - y‖ := by simp [dist_eq_norm, norm_sub_rev]
    _ = ‖(x - y) - (x - z)‖ := by rw [hvec]
    _ = ‖pointToComplex ((x - y) - (x - z))‖ :=
      (pointToComplex.norm_map _).symm
    _ = dist u v := by rw [map_sub, dist_eq_norm]
    _ = r := hdist

end Erdos957
