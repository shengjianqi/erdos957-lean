import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Uniform vertical separation of three well-spaced directions in a semicircle. -/

namespace Erdos957

/-- In the open right semicircle, an angular gap of at least 60 degrees raises
the sine coordinate by at least one half. Endpoints may be included here. -/
theorem sine_gap_ge_half (x y : ℝ)
    (hx : -Real.pi / 2 ≤ x) (hy : y ≤ Real.pi / 2)
    (hgap : Real.pi / 3 ≤ y - x) :
    (1 / 2 : ℝ) ≤ Real.sin y - Real.sin x := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hdlo : Real.pi / 6 ≤ (y - x) / 2 := by linarith
  have hdhi : (y - x) / 2 ≤ Real.pi / 2 := by linarith
  have hmlo : -Real.pi / 3 ≤ (y + x) / 2 := by linarith
  have hmhi : (y + x) / 2 ≤ Real.pi / 3 := by linarith
  have hsin : (1 / 2 : ℝ) ≤ Real.sin ((y - x) / 2) := by
    rw [← Real.sin_pi_div_six]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hdhi hdlo
  have hmabs : |(y + x) / 2| ≤ Real.pi / 3 :=
    abs_le.mpr ⟨by linarith, hmhi⟩
  have hcos : (1 / 2 : ℝ) ≤ Real.cos ((y + x) / 2) := by
    calc
      (1 / 2 : ℝ) = Real.cos (Real.pi / 3) := Real.cos_pi_div_three.symm
      _ ≤ Real.cos |(y + x) / 2| :=
        Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith) hmabs
      _ = Real.cos ((y + x) / 2) := Real.cos_abs _
  rw [Real.sin_sub_sin]
  nlinarith [mul_nonneg (sub_nonneg.mpr hsin) (sub_nonneg.mpr hcos)]

/-- Three directions separated by at least 60 degrees inside the open right
semicircle place the middle direction within 30 degrees of horizontal and
separate its sine coordinate from both neighbors by at least one half. -/
theorem middle_sine_gaps_ge_half (α β γ : ℝ)
    (hα : -Real.pi / 2 < α) (hγ : γ < Real.pi / 2)
    (hαβ : Real.pi / 3 ≤ β - α)
    (hβγ : Real.pi / 3 ≤ γ - β) :
    (-Real.pi / 6 < β ∧ β < Real.pi / 6) ∧
      (1 / 2 : ℝ) ≤ Real.sin β - Real.sin α ∧
      (1 / 2 : ℝ) ≤ Real.sin γ - Real.sin β := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hβlo : -Real.pi / 6 < β := by linarith
  have hβhi : β < Real.pi / 6 := by linarith
  refine ⟨⟨hβlo, hβhi⟩, ?_, ?_⟩
  · exact sine_gap_ge_half α β hα.le (by linarith) hαβ
  · exact sine_gap_ge_half β γ (by linarith) hγ.le hβγ

end Erdos957
