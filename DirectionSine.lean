import RadialAngles

/-! Positive complex cross products and lifted real direction angles. -/

namespace Erdos957

open scoped ComplexConjugate

/-- A positive complex cross product gives a positive sine of any real angle
lift representing the two principal arguments. -/
theorem sin_sub_pos_of_im_conj_mul_pos (u v : ℂ) (α β : ℝ)
    (hα : (α : Real.Angle) = (u.arg : Real.Angle))
    (hβ : (β : Real.Angle) = (v.arg : Real.Angle))
    (hcross : 0 < (conj u * v).im) :
    0 < Real.sin (β - α) := by
  have hang : ((β - α : ℝ) : Real.Angle) =
      ((v.arg - u.arg : ℝ) : Real.Angle) := by
    rw [Real.Angle.coe_sub, Real.Angle.coe_sub, hβ, hα]
  have hsin : Real.sin (β - α) = Real.sin (v.arg - u.arg) := by
    calc
      Real.sin (β - α) = Real.Angle.sin ((β - α : ℝ) : Real.Angle) :=
        (Real.Angle.sin_coe _).symm
      _ = Real.Angle.sin ((v.arg - u.arg : ℝ) : Real.Angle) := by rw [hang]
      _ = Real.sin (v.arg - u.arg) := Real.Angle.sin_coe _
  have hnorm : 0 ≤ ‖u‖ * ‖v‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hcross' := im_conj_mul_eq_norm_mul_sin_arg_sub u v
  have hpos : 0 < Real.sin (v.arg - u.arg) := by
    by_contra h
    have hle : Real.sin (v.arg - u.arg) ≤ 0 := le_of_not_gt h
    have hprod : ‖u‖ * ‖v‖ * Real.sin (v.arg - u.arg) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hnorm hle
    linarith
  rwa [hsin]

/-- The cross product of two consecutive edge vectors is the three-point
signed turn. -/
theorem turn_eq_im_conj_mul_edges (a b d : Point) :
    turn a b d =
      (conj (pointToComplex (b - a)) * pointToComplex (d - b)).im := by
  simp only [pointToComplex, Complex.orthonormalBasisOneI_repr_symm_apply]
  simp [turn, Complex.mul_im]
  ring

end Erdos957
