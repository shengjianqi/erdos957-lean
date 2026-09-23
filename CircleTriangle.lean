import RadialAngles

/-! Strict orientation of short circle arcs and triangles with a distant axis point. -/

namespace Erdos957

open scoped ComplexConjugate

def complexTurn (a b c : ℂ) : ℝ := (conj (b - a) * (c - a)).im

theorem complexTurn_cross_sum (a b c : ℂ) :
    complexTurn a b c = (conj a * b).im + (conj b * c).im - (conj a * c).im := by
  simp [complexTurn, Complex.mul_im]
  ring

theorem complexTurn_cyclic (a b c : ℂ) : complexTurn c a b = complexTurn a b c := by
  simp [complexTurn, Complex.mul_im]
  ring

private theorem sin_add_lt_sum (x y : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hxπ : x < Real.pi) (hyπ : y < Real.pi) :
    Real.sin (x + y) < Real.sin x + Real.sin y := by
  have hsx := Real.sin_pos_of_pos_of_lt_pi hx hxπ
  have hsy := Real.sin_pos_of_pos_of_lt_pi hy hyπ
  have hcy : Real.cos y < 1 := by
    simpa using Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl (0 : ℝ)) hyπ.le hy
  have hfirst := mul_lt_mul_of_pos_left hcy hsx
  have hsecond := mul_le_mul_of_nonneg_right (Real.cos_le_one x) hsy.le
  rw [Real.sin_add]
  nlinarith

/-- Three points in strict angular order on a short circle arc turn left. -/
theorem circle_three_arg_turn_pos (a b c : ℂ) (R : ℝ) (hR : 0 < R)
    (ha : ‖a‖ = R) (hb : ‖b‖ = R) (hc : ‖c‖ = R)
    (hab : a.arg < b.arg) (hbc : b.arg < c.arg)
    (hspan : c.arg - a.arg < Real.pi) : 0 < complexTurn a b c := by
  have hsin := sin_add_lt_sum (b.arg - a.arg) (c.arg - b.arg)
    (sub_pos.mpr hab) (sub_pos.mpr hbc) (by linarith) (by linarith)
  rw [show b.arg - a.arg + (c.arg - b.arg) = c.arg - a.arg by ring] at hsin
  have hprod := mul_pos (sq_pos_of_pos hR)
    (show 0 < Real.sin (b.arg - a.arg) + Real.sin (c.arg - b.arg) -
      Real.sin (c.arg - a.arg) by linarith)
  rw [complexTurn_cross_sum]
  simp only [im_conj_mul_eq_norm_mul_sin_arg_sub, ha, hb, hc]
  nlinarith

theorem abs_complex_cross_le_sq (a b : ℂ) (R : ℝ)
    (ha : ‖a‖ = R) (hb : ‖b‖ = R) : |(conj a * b).im| ≤ R ^ 2 := by
  calc
    |(conj a * b).im| ≤ ‖conj a * b‖ := Complex.abs_im_le_norm _
    _ = R ^ 2 := by simp [ha, hb, pow_two]

/-- A real-axis point farther than twice the circle radius lies beyond both
chords from a middle point with vertical gaps at least half the radius. -/
theorem circle_middle_far_axis_turns (a b c : ℂ) (R L : ℝ) (hR : 0 < R)
    (ha : ‖a‖ = R) (hb : ‖b‖ = R) (hc : ‖c‖ = R)
    (hab : R / 2 ≤ b.im - a.im) (hbc : R / 2 ≤ c.im - b.im)
    (hL : 2 * R < L) :
    0 < complexTurn a (L : ℂ) b ∧ 0 < complexTurn (L : ℂ) c b := by
  have hLpos : 0 < L := by linarith
  have habcross := (abs_le.mp (abs_complex_cross_le_sq a b R ha hb)).2
  have hbccross := (abs_le.mp (abs_complex_cross_le_sq b c R hb hc)).2
  have hprod : R ^ 2 < L * (R / 2) := by
    nlinarith [mul_pos (sub_pos.mpr hL) hR]
  have hdyab := mul_le_mul_of_nonneg_left hab hLpos.le
  have hdybc := mul_le_mul_of_nonneg_left hbc hLpos.le
  have hfirst : complexTurn a (L : ℂ) b =
      L * (b.im - a.im) - (conj a * b).im := by
    simp [complexTurn, Complex.mul_im]
    ring
  have hsecond : complexTurn (L : ℂ) c b =
      L * (c.im - b.im) - (conj b * c).im := by
    simp [complexTurn, Complex.mul_im]
    ring
  rw [hfirst, hsecond]
  constructor <;> linarith

end Erdos957
