import NormalizedEdge
import RadialAngles
import Mathlib.Tactic.Ring

/-! Signed area and affine identities in coordinates normalized by an edge. -/

namespace Erdos957

open scoped ComplexConjugate

theorem edgeCoordinate_injective (u v : Point) (hne : u ≠ v) :
    Function.Injective (edgeCoordinate u v) := by
  intro x y hxy
  have hzero : dist x y / dist u v = 0 := by
    rw [← edgeCoordinate_dist u v x y hne, hxy, dist_self]
  have hdist : dist x y = 0 :=
    (div_eq_zero_iff.mp hzero).resolve_right (dist_ne_zero.mpr hne)
  exact dist_eq_zero.mp hdist

theorem edgeCoordinate_add_eq_of_add_eq (u v a b c d : Point)
    (h : a + b = c + d) :
    edgeCoordinate u v a + edgeCoordinate u v b =
      edgeCoordinate u v c + edgeCoordinate u v d := by
  simp only [edgeCoordinate, ← add_div, ← map_add]
  congr 1
  have hvec : (a - u) + (b - u) = (c - u) + (d - u) := by
    calc
      (a - u) + (b - u) = a + b - (u + u) := by abel
      _ = c + d - (u + u) := by rw [h]
      _ = (c - u) + (d - u) := by abel
  rw [hvec]

theorem edgeCoordinate_im_mul_dist_sq (u v x : Point) (hne : u ≠ v) :
    (edgeCoordinate u v x).im * dist u v ^ 2 = turn u v x := by
  have hnorm : Complex.normSq (pointToComplex (v - u)) = dist u v ^ 2 := by
    rw [Complex.normSq_eq_norm_sq, pointToComplex.norm_map]
    simp only [dist_eq_norm, norm_sub_rev]
  rw [turn_eq_im_conj_mul]
  simp only [edgeCoordinate, Complex.div_im, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, hnorm]
  field_simp [dist_ne_zero.mpr hne]
  ring

theorem edgeCoordinate_im_nonpos_of_support (u v x : Point)
    (hne : u ≠ v) (hsupport : 0 ≤ turn v u x) :
    (edgeCoordinate u v x).im ≤ 0 := by
  have hturn : turn u v x = -turn v u x := by
    unfold turn
    ring
  have hprod := edgeCoordinate_im_mul_dist_sq u v x hne
  rw [hturn] at hprod
  have hpositive : 0 < dist u v ^ 2 := sq_pos_of_pos (dist_pos.mpr hne)
  nlinarith

/-- The lower equilateral vertex of a normalized unit edge has these exact
coordinates; the height is represented algebraically to avoid square roots. -/
theorem unit_triangle_below_real_axis (z : ℂ)
    (hz : ‖z‖ = 1) (hz1 : ‖z - 1‖ = 1) (hbelow : z.im ≤ 0) :
    ∃ h : ℝ, 0 < h ∧ h ^ 2 = 3 / 4 ∧
      z = (1 / 2 : ℂ) - (h : ℂ) * Complex.I := by
  have hsq : z.re ^ 2 + z.im ^ 2 = 1 := by
    have h := Complex.normSq_eq_norm_sq z
    rw [Complex.normSq_apply, hz] at h
    nlinarith
  have hsq1 : (z.re - 1) ^ 2 + z.im ^ 2 = 1 := by
    have h := Complex.normSq_eq_norm_sq (z - 1)
    rw [Complex.normSq_apply, hz1] at h
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
      sub_zero] at h
    nlinarith
  have hre : z.re = 1 / 2 := by nlinarith
  refine ⟨-z.im, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · apply Complex.ext <;> simp [hre]

end Erdos957
