import EdgeAngleLift
import Mathlib.Tactic.Linarith

/-! Short successive turns add without crossing the principal-argument cut. -/

namespace Erdos957

private theorem pi_div_1800_pos : (0 : ℝ) < Real.pi / 1800 := by
  positivity

private theorem three_pi_div_1800_lt_pi : 3 * (Real.pi / 1800) < Real.pi := by
  have hpi := Real.pi_pos
  linarith

/-- Two short positive quotient arguments add as real principal arguments. -/
theorem arg_div_short_chain_two {z0 z1 z2 : ℂ}
    (hz0 : z0 ≠ 0) (hz1 : z1 ≠ 0) (hz2 : z2 ≠ 0)
    (h01 : 0 < (z1 / z0).arg ∧ (z1 / z0).arg < Real.pi / 1800)
    (h12 : 0 < (z2 / z1).arg ∧ (z2 / z1).arg < Real.pi / 1800) :
    0 < (z2 / z0).arg ∧ (z2 / z0).arg < 2 * (Real.pi / 1800) := by
  let δ : ℝ := (z1 / z0).arg + (z2 / z1).arg
  have hδ : 0 < δ ∧ δ < Real.pi := by
    dsimp [δ]
    constructor
    · linarith [h01.1, h12.1]
    · linarith [h01.2, h12.2, three_pi_div_1800_lt_pi]
  have hangle : (δ : Real.Angle) =
      (z2.arg : Real.Angle) - (z0.arg : Real.Angle) := by
    dsimp [δ]
    rw [Complex.arg_div_coe_angle hz1 hz0,
      Complex.arg_div_coe_angle hz2 hz1]
    abel
  rw [arg_div_eq_of_short_lift hz0 hz2 δ hδ hangle]
  dsimp [δ]
  constructor
  · linarith [h01.1, h12.1]
  · linarith [h01.2, h12.2]

/-- Three short positive quotient arguments also remain within the principal branch. -/
theorem arg_div_short_chain_three {z0 z1 z2 z3 : ℂ}
    (hz0 : z0 ≠ 0) (hz1 : z1 ≠ 0) (hz2 : z2 ≠ 0) (hz3 : z3 ≠ 0)
    (h01 : 0 < (z1 / z0).arg ∧ (z1 / z0).arg < Real.pi / 1800)
    (h12 : 0 < (z2 / z1).arg ∧ (z2 / z1).arg < Real.pi / 1800)
    (h23 : 0 < (z3 / z2).arg ∧ (z3 / z2).arg < Real.pi / 1800) :
    0 < (z3 / z0).arg ∧ (z3 / z0).arg < 3 * (Real.pi / 1800) := by
  have h02 := arg_div_short_chain_two hz0 hz1 hz2 h01 h12
  let δ : ℝ := (z2 / z0).arg + (z3 / z2).arg
  have hδ : 0 < δ ∧ δ < Real.pi := by
    dsimp [δ]
    constructor
    · linarith [h02.1, h23.1]
    · linarith [h02.2, h23.2, three_pi_div_1800_lt_pi]
  have hangle : (δ : Real.Angle) =
      (z3.arg : Real.Angle) - (z0.arg : Real.Angle) := by
    dsimp [δ]
    rw [Complex.arg_div_coe_angle hz2 hz0,
      Complex.arg_div_coe_angle hz3 hz2]
    abel
  rw [arg_div_eq_of_short_lift hz0 hz3 δ hδ hangle]
  dsimp [δ]
  constructor
  · linarith [h02.1, h23.1]
  · linarith [h02.2, h23.2]

/-- Reversing a quotient preserves the absolute principal argument, even at a cut. -/
theorem abs_arg_div_reverse_eq (z w : ℂ) :
    |(z / w).arg| = |(w / z).arg| := by
  have h : (w / z)⁻¹ = z / w := by
    simp [inv_div]
  rw [← h, Complex.abs_arg_inv]

/-- The first three forward and reverse links from the initial edge are short. -/
theorem short_chain_forward_reverse_abs_le {z0 z1 z2 z3 : ℂ}
    (hz0 : z0 ≠ 0) (hz1 : z1 ≠ 0) (hz2 : z2 ≠ 0) (hz3 : z3 ≠ 0)
    (h01 : 0 < (z1 / z0).arg ∧ (z1 / z0).arg < Real.pi / 1800)
    (h12 : 0 < (z2 / z1).arg ∧ (z2 / z1).arg < Real.pi / 1800)
    (h23 : 0 < (z3 / z2).arg ∧ (z3 / z2).arg < Real.pi / 1800) :
    (∀ z ∈ ({z1, z2, z3} : Set ℂ),
      |(z / z0).arg| ≤ Real.pi / 600 ∧
      |(z0 / z).arg| ≤ Real.pi / 600) := by
  have h02 := arg_div_short_chain_two hz0 hz1 hz2 h01 h12
  have h03 := arg_div_short_chain_three hz0 hz1 hz2 hz3 h01 h12 h23
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with hz | hz | hz
  · rw [hz]
    have hbound : |(z1 / z0).arg| ≤ Real.pi / 600 := by
      rw [abs_of_pos h01.1]
      linarith [h01.2, pi_div_1800_pos]
    exact ⟨hbound, (abs_arg_div_reverse_eq z0 z1).trans_le hbound⟩
  · rw [hz]
    have hbound : |(z2 / z0).arg| ≤ Real.pi / 600 := by
      rw [abs_of_pos h02.1]
      linarith [h02.2, pi_div_1800_pos]
    exact ⟨hbound, (abs_arg_div_reverse_eq z0 z2).trans_le hbound⟩
  · rw [hz]
    have hbound : |(z3 / z0).arg| ≤ Real.pi / 600 := by
      rw [abs_of_pos h03.1]
      linarith [h03.2, pi_div_1800_pos]
    exact ⟨hbound, (abs_arg_div_reverse_eq z0 z3).trans_le hbound⟩

end Erdos957
