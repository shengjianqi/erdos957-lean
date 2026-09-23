import Mathlib.Analysis.Complex.Angle
import Mathlib.Tactic.Linarith
import PlanarDirections

/-! Converting a positive oriented exterior turn into a Euclidean interior angle. -/

namespace Erdos957

open InnerProductGeometry

/-- For consecutive nonzero complex edge vectors, the interior angle at their
shared vertex is the supplement of the positive exterior angle. -/
theorem complex_interior_angle_eq_pi_sub_exterior
    (e_prev e : ℂ) (hprev : e_prev ≠ 0) (he : e ≠ 0)
    (hδpos : 0 < (e / e_prev).arg) :
    angle (-e_prev) e = Real.pi - (e / e_prev).arg := by
  calc
    angle (-e_prev) e = Real.pi - angle e_prev e := angle_neg_left e_prev e
    _ = Real.pi - angle e e_prev := by rw [angle_comm]
    _ = Real.pi - |(e / e_prev).arg| := by
      rw [Complex.angle_eq_abs_arg he hprev]
    _ = Real.pi - (e / e_prev).arg := by rw [abs_of_pos hδpos]

/-- An exterior turn below one degree corresponds to a Euclidean interior
angle strictly between 179 and 180 degrees. -/
theorem complex_interior_angle_gt_179_of_exterior_lt_one_degree
    (e_prev e : ℂ) (hprev : e_prev ≠ 0) (he : e ≠ 0)
    (hδpos : 0 < (e / e_prev).arg)
    (hδone : (e / e_prev).arg < Real.pi / 180) :
    Real.pi - Real.pi / 180 < angle (-e_prev) e ∧
      angle (-e_prev) e < Real.pi := by
  rw [complex_interior_angle_eq_pi_sub_exterior e_prev e hprev he hδpos]
  constructor <;> linarith

/-- The geometric angle at the middle point equals the supplement of the
positive turn between the incoming and outgoing edge directions. -/
theorem point_interior_angle_eq_pi_sub_exterior
    (a b c : Point) (hab : a ≠ b) (hbc : b ≠ c)
    (hδpos : 0 <
      (pointToComplex (c - b) / pointToComplex (b - a)).arg) :
    angle (a - b) (c - b) = Real.pi -
      (pointToComplex (c - b) / pointToComplex (b - a)).arg := by
  have hprev : pointToComplex (b - a) ≠ 0 := by
    intro hz
    have hba : b - a = 0 := pointToComplex.injective (by simpa using hz)
    exact hab (sub_eq_zero.mp hba).symm
  have hcur : pointToComplex (c - b) ≠ 0 := by
    intro hz
    have hcb : c - b = 0 := pointToComplex.injective (by simpa using hz)
    exact hbc (sub_eq_zero.mp hcb).symm
  have hrev : pointToComplex (a - b) = -pointToComplex (b - a) := by
    rw [← map_neg]
    congr 1
    abel
  calc
    angle (a - b) (c - b) =
        angle (pointToComplex (a - b)) (pointToComplex (c - b)) :=
      (pointToComplex.toLinearIsometry.angle_map (a - b) (c - b)).symm
    _ = angle (-pointToComplex (b - a)) (pointToComplex (c - b)) := by rw [hrev]
    _ = Real.pi - (pointToComplex (c - b) / pointToComplex (b - a)).arg :=
      complex_interior_angle_eq_pi_sub_exterior _ _ hprev hcur hδpos

/-- A hull turn below one degree gives the actual three-point Euclidean
angle at the vertex strictly between 179 and 180 degrees. -/
theorem point_interior_angle_gt_179_of_exterior_lt_one_degree
    (a b c : Point) (hab : a ≠ b) (hbc : b ≠ c)
    (hδpos : 0 <
      (pointToComplex (c - b) / pointToComplex (b - a)).arg)
    (hδone : (pointToComplex (c - b) / pointToComplex (b - a)).arg <
      Real.pi / 180) :
    Real.pi - Real.pi / 180 < angle (a - b) (c - b) ∧
      angle (a - b) (c - b) < Real.pi := by
  rw [point_interior_angle_eq_pi_sub_exterior a b c hab hbc hδpos]
  constructor <;> linarith

end Erdos957
