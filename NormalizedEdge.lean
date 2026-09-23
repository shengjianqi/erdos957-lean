import RotatedCoordinates
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! Complex coordinates normalized by an oriented nonzero planar edge. -/

namespace Erdos957

open scoped ComplexConjugate

/-- Send `u` to zero and `v` to one by a complex similarity. -/
noncomputable def edgeCoordinate (u v x : Point) : ℂ :=
  pointToComplex (x - u) / pointToComplex (v - u)

private theorem edge_den_ne_zero (u v : Point) (hne : u ≠ v) :
    pointToComplex (v - u) ≠ 0 := by
  intro hz
  have hsub : v - u = 0 := pointToComplex.injective (by simpa using hz)
  exact hne (sub_eq_zero.mp hsub).symm

theorem edgeCoordinate_self (u v : Point) : edgeCoordinate u v u = 0 := by
  simp [edgeCoordinate]

theorem edgeCoordinate_axis (u v : Point) (hne : u ≠ v) :
    edgeCoordinate u v v = 1 := by
  change pointToComplex (v - u) / pointToComplex (v - u) = 1
  exact div_self (edge_den_ne_zero u v hne)

theorem edgeCoordinate_dist (u v x y : Point) (_hne : u ≠ v) :
    dist (edgeCoordinate u v x) (edgeCoordinate u v y) =
      dist x y / dist u v := by
  have hdiff : edgeCoordinate u v x - edgeCoordinate u v y =
      pointToComplex (x - y) / pointToComplex (v - u) := by
    simp only [edgeCoordinate, ← sub_div, ← map_sub]
    congr 1
    abel_nf
  rw [dist_eq_norm, hdiff, norm_div, pointToComplex.norm_map,
    pointToComplex.norm_map]
  simp only [dist_eq_norm, norm_sub_rev]

theorem edgeCoordinate_norm (u v x : Point) (_hne : u ≠ v) :
    ‖edgeCoordinate u v x‖ = dist u x / dist u v := by
  rw [edgeCoordinate, norm_div, pointToComplex.norm_map,
    pointToComplex.norm_map]
  simp only [dist_eq_norm, norm_sub_rev]

theorem edgeCoordinate_sub_one_norm (u v x : Point) (hne : u ≠ v) :
    ‖edgeCoordinate u v x - 1‖ = dist v x / dist u v := by
  rw [← edgeCoordinate_axis u v hne, ← dist_eq_norm]
  rw [edgeCoordinate_dist u v x v hne]
  simp only [dist_comm]

/-- Within one common strict half-plane, the principal argument of the
normalized edge coordinate is exactly the difference of the two half-plane
arguments, without a branch-cut correction. -/
theorem edgeCoordinate_arg (u v x axis : Point)
    (hvhalf : 0 < inner ℝ axis (v - u))
    (hxhalf : 0 < inner ℝ axis (x - u)) :
    (edgeCoordinate u v x).arg =
      halfplaneArg u axis x - halfplaneArg u axis v := by
  have haxis : axis ≠ 0 := by
    intro hz
    simp [hz] at hvhalf
  have hvsub : v - u ≠ 0 := by
    intro hz
    simp [hz] at hvhalf
  have hxsub : x - u ≠ 0 := by
    intro hz
    simp [hz] at hxhalf
  have hA : pointToComplex axis ≠ 0 := by
    intro hz
    exact haxis (pointToComplex.injective (by simpa using hz))
  have hV : pointToComplex (v - u) ≠ 0 := by
    intro hz
    exact hvsub (pointToComplex.injective (by simpa using hz))
  have hX : pointToComplex (x - u) ≠ 0 := by
    intro hz
    exact hxsub (pointToComplex.injective (by simpa using hz))
  have hconj : conj (pointToComplex axis) ≠ 0 := by
    intro hz
    apply hA
    have hzz := congrArg conj hz
    simpa using hzz
  have hrotV : rotatedCoordinate u axis v ≠ 0 :=
    mul_ne_zero hconj hV
  have hrotX : rotatedCoordinate u axis x ≠ 0 :=
    mul_ne_zero hconj hX
  have hratio : edgeCoordinate u v x =
      rotatedCoordinate u axis x / rotatedCoordinate u axis v := by
    simp only [edgeCoordinate, rotatedCoordinate]
    rw [mul_div_mul_left _ _ hconj]
  have hangle : ((edgeCoordinate u v x).arg : Real.Angle) =
      ((halfplaneArg u axis x - halfplaneArg u axis v : ℝ) : Real.Angle) := by
    rw [hratio, Complex.arg_div_coe_angle hrotX hrotV,
      Real.Angle.coe_sub]
    rfl
  have hxI := halfplaneArg_mem_Ioo hxhalf
  have hvI := halfplaneArg_mem_Ioo hvhalf
  have hgapI : halfplaneArg u axis x - halfplaneArg u axis v ∈
      Set.Ioc (-Real.pi) Real.pi := by
    constructor <;> linarith
  exact (Complex.arg_coe_angle_eq_iff_eq_toReal.mp hangle).trans
    (Real.Angle.toReal_coe_eq_self_iff_mem_Ioc.mpr hgapI)

end Erdos957
