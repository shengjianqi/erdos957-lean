import RadialAngles
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Relative argument of an oriented chord between two radial points. -/

namespace Erdos957

open scoped ComplexConjugate

/-- In the upper half-plane, shifting left by one strictly increases the
principal argument, while keeping it below π. -/
theorem complex_arg_sub_one_between {t : ℂ} (ht : 0 < t.im) :
    0 < t.arg ∧ t.arg < (t - 1).arg ∧ (t - 1).arg < Real.pi := by
  have ht0 : 0 ≤ t.arg := Complex.arg_nonneg_iff.mpr ht.le
  have htne : t.arg ≠ 0 := by
    intro h
    have him : t.im = 0 := (Complex.arg_eq_zero_iff.mp h).2
    linarith
  have htpos : 0 < t.arg := lt_of_le_of_ne ht0 (Ne.symm htne)
  have htim : (t - 1).im = t.im := by simp
  have hsubnonneg : 0 ≤ (t - 1).arg :=
    Complex.arg_nonneg_iff.mpr (by linarith)
  have hupper : (t - 1).arg < Real.pi := by
    apply Complex.arg_lt_pi_iff.mpr
    right
    exact ne_of_gt (htim ▸ ht)
  have hcross : 0 < (conj t * (t - 1)).im := by
    simp [Complex.mul_im]
    nlinarith [Complex.mul_conj t]
  have hsin : 0 < Real.sin ((t - 1).arg - t.arg) := by
    rw [im_conj_mul_eq_norm_mul_sin_arg_sub] at hcross
    by_contra hn
    have hnonpos := mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (norm_nonneg t) (norm_nonneg (t - 1))) (le_of_not_gt hn)
    linarith
  have hdiff : t.arg < (t - 1).arg := by
    by_contra hn
    have hnonpos : Real.sin ((t - 1).arg - t.arg) ≤ 0 :=
      Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith)
        (by linarith [Complex.arg_le_pi t])
    linarith
  exact ⟨htpos, hdiff, hupper⟩

/-- A short positive lift of the relative angle is exactly the principal
argument of the quotient. -/
theorem arg_div_eq_of_short_lift {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0)
    (δ : ℝ) (hδ : 0 < δ ∧ δ < Real.pi)
    (hangle : (δ : Real.Angle) =
      (w.arg : Real.Angle) - (z.arg : Real.Angle)) :
    (w / z).arg = δ := by
  have hco : ((w / z).arg : Real.Angle) = (δ : Real.Angle) := by
    rw [Complex.arg_div_coe_angle hw hz]
    exact hangle.symm
  have hδI : δ ∈ Set.Ioc (-Real.pi) Real.pi := by
    constructor <;> linarith [Real.pi_pos]
  exact (Complex.arg_coe_angle_eq_iff_eq_toReal.mp hco).trans
    (Real.Angle.toReal_coe_eq_self_iff.mpr hδI)

/-- The oriented chord has a relative angle strictly between the later
radius and a half-turn from the earlier radius. -/
theorem edge_ratio_arg_between {z w : ℂ} (hz : z ≠ 0)
    (hcross : 0 < (conj z * w).im) :
    0 < (w / z).arg ∧
      (w / z).arg < ((w - z) / z).arg ∧
      ((w - z) / z).arg < Real.pi := by
  have hquotim : (w / z).im = (conj z * w).im / Complex.normSq z := by
    simp [Complex.div_im, Complex.mul_im]
    ring
  have ht : 0 < (w / z).im := by
    rw [hquotim]
    exact div_pos hcross (Complex.normSq_pos.mpr hz)
  have hsub : w / z - 1 = (w - z) / z := by
    field_simp
  have hbetween := complex_arg_sub_one_between ht
  rw [hsub] at hbetween
  exact hbetween

/-- The real lift of an oriented chord represents its true complex direction
modulo a whole turn. -/
theorem edge_lift_coe_angle {z w : ℂ} (hz : z ≠ 0) (hzw : w ≠ z) :
    ((z.arg + ((w - z) / z).arg : ℝ) : Real.Angle) =
      ((w - z).arg : Real.Angle) := by
  have hq : (w - z) / z ≠ 0 := div_ne_zero (sub_ne_zero.mpr hzw) hz
  have hmul : z * ((w - z) / z) = w - z := by
    field_simp
  calc
    ((z.arg + ((w - z) / z).arg : ℝ) : Real.Angle) =
        (z.arg : Real.Angle) + (((w - z) / z).arg : Real.Angle) := by
          rw [Real.Angle.coe_add]
    _ = ((z * ((w - z) / z)).arg : Real.Angle) :=
      (Complex.arg_mul_coe_angle hz hq).symm
    _ = ((w - z).arg : Real.Angle) := by rw [hmul]

end Erdos957
