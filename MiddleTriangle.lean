import MiddleAngleBounds
import CircleTriangle
import RotatedCoordinates
import TriangleInterior

/-! The middle point of three separated circle directions is an interior point
of the triangle formed by its two neighbors and a sufficiently distant axis point. -/

namespace Erdos957

open scoped ComplexConjugate

theorem circle_middle_mem_interior_triangle
    (x axis a b c : Point) (r : ℝ) (hr : 0 < r)
    (ha : dist x a = r) (hb : dist x b = r) (hc : dist x c = r)
    (hα : -Real.pi / 2 < halfplaneArg x axis a)
    (hγ : halfplaneArg x axis c < Real.pi / 2)
    (hab : Real.pi / 3 ≤ halfplaneArg x axis b - halfplaneArg x axis a)
    (hbc : Real.pi / 3 ≤ halfplaneArg x axis c - halfplaneArg x axis b)
    (hlarge : 2 * r < ‖axis‖) :
    b ∈ interior (convexHull ℝ ({a, x + axis, c} : Set Point)) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hD : 0 < ‖axis‖ := by linarith
  have haxis : axis ≠ 0 := norm_pos_iff.mp hD
  let R : ℝ := ‖axis‖ * r
  let A := rotatedCoordinate x axis a
  let B := rotatedCoordinate x axis b
  let C := rotatedCoordinate x axis c
  have hR : 0 < R := mul_pos hD hr
  have hA : ‖A‖ = R := rotatedCoordinate_norm_of_dist x axis a r ha
  have hB : ‖B‖ = R := rotatedCoordinate_norm_of_dist x axis b r hb
  have hC : ‖C‖ = R := rotatedCoordinate_norm_of_dist x axis c r hc
  obtain ⟨_, hsab, hsbc⟩ := middle_sine_gaps_ge_half
    (halfplaneArg x axis a) (halfplaneArg x axis b) (halfplaneArg x axis c)
    hα hγ hab hbc
  have himA : A.im = R * Real.sin (halfplaneArg x axis a) :=
    rotatedCoordinate_im_of_dist x axis a r ha
  have himB : B.im = R * Real.sin (halfplaneArg x axis b) :=
    rotatedCoordinate_im_of_dist x axis b r hb
  have himC : C.im = R * Real.sin (halfplaneArg x axis c) :=
    rotatedCoordinate_im_of_dist x axis c r hc
  have hvab : R / 2 ≤ B.im - A.im := by
    rw [himA, himB]
    nlinarith [mul_le_mul_of_nonneg_left hsab hR.le]
  have hvbc : R / 2 ≤ C.im - B.im := by
    rw [himB, himC]
    nlinarith [mul_le_mul_of_nonneg_left hsbc hR.le]
  have hfar : 2 * R < ‖axis‖ ^ 2 := by
    dsimp only [R]
    nlinarith [mul_pos (sub_pos.mpr hlarge) hD]
  obtain ⟨htab, htcb⟩ := circle_middle_far_axis_turns A B C R (‖axis‖ ^ 2)
    hR hA hB hC hvab hvbc hfar
  have harcab : A.arg < B.arg := by
    change halfplaneArg x axis a < halfplaneArg x axis b
    linarith
  have harcbc : B.arg < C.arg := by
    change halfplaneArg x axis b < halfplaneArg x axis c
    linarith
  have hspan : C.arg - A.arg < Real.pi := by
    change halfplaneArg x axis c - halfplaneArg x axis a < Real.pi
    linarith
  have hcircle := circle_three_arg_turn_pos A B C R hR hA hB hC
    harcab harcbc hspan
  have htab' : 0 < turn a (x + axis) b := by
    apply (rotatedCoordinate_turn_pos_iff x axis a (x + axis) b haxis).mp
    simpa only [complexTurn, A, B, rotatedCoordinate_axis] using htab
  have htcb' : 0 < turn (x + axis) c b := by
    apply (rotatedCoordinate_turn_pos_iff x axis (x + axis) c b haxis).mp
    simpa only [complexTurn, B, C, rotatedCoordinate_axis] using htcb
  have hcab : 0 < turn c a b := by
    apply (rotatedCoordinate_turn_pos_iff x axis c a b haxis).mp
    change 0 < complexTurn C A B
    rwa [complexTurn_cyclic]
  have hsum : turn a (x + axis) b + turn (x + axis) c b + turn c a b =
      turn a (x + axis) c := by
    unfold turn
    ring
  exact triangle_strict_turns_mem_interior a (x + axis) c b
    (by linarith) htab' htcb' hcab

end Erdos957
