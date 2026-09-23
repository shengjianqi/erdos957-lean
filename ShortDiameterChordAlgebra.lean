import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-! Scalar geometry for a shortest chord joining two diameter endpoints.
The chord is placed from `(0,0)` to `(r,0)`. -/

namespace Erdos957

/-- If two diameter axes point below a shortest chord, any configuration
point strictly above the chord would force the axes to have negative inner
product. No convexity or flat-neighborhood hypothesis is used. -/
theorem short_chord_opposite_point_axes_inner_neg
    (r a b c d x y : ℝ)
    (_hr : 0 < r) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (hy : 0 < y)
    (hminu : r ^ 2 ≤ x ^ 2 + y ^ 2)
    (hminw : r ^ 2 ≤ (x - r) ^ 2 + y ^ 2)
    (hju : 0 < a * x - b * y)
    (hkw : 0 < c * (r - x) - d * y) :
    -(a * c) + b * d < 0 := by
  have hax : 0 < a * x := by nlinarith [mul_pos hb hy]
  have hx : 0 < x := (mul_pos_iff_of_pos_left ha).mp hax
  have hcx : 0 < c * (r - x) := by nlinarith [mul_pos hd hy]
  have hrx : 0 < r - x := (mul_pos_iff_of_pos_left hc).mp hcx
  have hxy : x ^ 2 ≤ y ^ 2 := by
    nlinarith [mul_nonneg hx.le hrx.le]
  have hrxy : (r - x) ^ 2 ≤ y ^ 2 := by
    nlinarith [mul_nonneg hx.le hrx.le]
  have hyx : x ≤ y := by
    by_contra h
    have hlt : y < x := lt_of_not_ge h
    nlinarith [mul_pos (sub_pos.mpr hlt) (show 0 < x + y by linarith)]
  have hyrx : r - x ≤ y := by
    by_contra h
    have hlt : y < r - x := lt_of_not_ge h
    nlinarith [mul_pos (sub_pos.mpr hlt) (show 0 < (r - x) + y by linarith)]
  have hba : b < a := by
    have hby := mul_le_mul_of_nonneg_left hyx hb.le
    by_contra h
    have hmul := mul_le_mul_of_nonneg_right (le_of_not_gt h) hx.le
    linarith
  have hdc : d < c := by
    have hdy := mul_le_mul_of_nonneg_left hyrx hd.le
    by_contra h
    have hmul := mul_le_mul_of_nonneg_right (le_of_not_gt h) hrx.le
    linarith
  have hprod : b * d < a * c :=
    (mul_lt_mul_of_pos_right hba hd).trans (mul_lt_mul_of_pos_left hdc ha)
  linarith

/-- Two vectors with positive right/left projections and transverse
components of opposite signs have negative inner product. -/
theorem short_chord_opposed_sides_axes_inner_neg
    (a b c d : ℝ) (ha : 0 < a) (hc : 0 < c) (hbd : b * d ≤ 0) :
    -(a * c) + b * d < 0 := by
  nlinarith [mul_pos ha hc]

/-- In coordinates with diameter partners `(a,b)` and `(r-c,d)`, positive
inner product of the two diameter axes forces every separated configuration
point to lie on the same side of the chord as the first partner. -/
theorem short_chord_point_same_side
    (r a b c d x y : ℝ)
    (hr : 0 < r) (ha : 0 < a) (hc : 0 < c)
    (hdot : 0 < -(a * c) + b * d)
    (hminu : r ^ 2 ≤ x ^ 2 + y ^ 2)
    (hminw : r ^ 2 ≤ (x - r) ^ 2 + y ^ 2)
    (hju : 0 < a * x + b * y)
    (hkw : 0 < c * (r - x) + d * y) :
    0 ≤ b * y := by
  have hbd : 0 < b * d := by nlinarith [mul_pos ha hc]
  by_contra h
  have hby : b * y < 0 := lt_of_not_ge h
  by_cases hb : 0 < b
  · have hd : 0 < d := (mul_pos_iff_of_pos_left hb).mp hbd
    have hy : y < 0 := by
      by_contra h
      have := mul_nonneg hb.le (le_of_not_gt h)
      linarith
    have hneg := short_chord_opposite_point_axes_inner_neg
      r a b c d x (-y) hr ha hb hc hd (by linarith)
      (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith)
    linarith
  · have hb' : b < 0 := by
      have hbne : b ≠ 0 := by intro h; simp [h] at hbd
      exact lt_of_le_of_ne (le_of_not_gt hb) hbne
    have hd : d < 0 := by
      by_contra h
      have := mul_nonpos_of_nonpos_of_nonneg hb'.le (le_of_not_gt h)
      linarith
    have hy : 0 < y := by
      by_contra h
      have := mul_nonneg_of_nonpos_of_nonpos hb'.le (le_of_not_gt h)
      linarith
    have hneg := short_chord_opposite_point_axes_inner_neg
      r a (-b) c (-d) x y hr ha (by linarith) hc (by linarith) hy
      hminu hminw (by nlinarith) (by nlinarith)
    nlinarith

/-- The side conclusion is strict for a point separated from both chord
endpoints. This also excludes additional configuration points on the chord
line. -/
theorem short_chord_point_strict_same_side
    (r a b c d x y : ℝ)
    (hr : 0 < r) (ha : 0 < a) (hc : 0 < c)
    (hdot : 0 < -(a * c) + b * d)
    (hminu : r ^ 2 ≤ x ^ 2 + y ^ 2)
    (hminw : r ^ 2 ≤ (x - r) ^ 2 + y ^ 2)
    (hju : 0 < a * x + b * y)
    (hkw : 0 < c * (r - x) + d * y) :
    0 < b * y := by
  have hside := short_chord_point_same_side r a b c d x y
    hr ha hc hdot hminu hminw hju hkw
  have hb : b ≠ 0 := by
    intro h
    subst b
    nlinarith [mul_pos ha hc]
  have hy : y ≠ 0 := by
    intro h
    subst y
    have hax : 0 < a * x := by simpa using hju
    have hx : 0 < x := (mul_pos_iff_of_pos_left ha).mp hax
    have hcx : 0 < c * (r - x) := by simpa using hkw
    have hrx : 0 < r - x := (mul_pos_iff_of_pos_left hc).mp hcx
    nlinarith [mul_pos hrx (add_pos hr hx)]
  exact lt_of_le_of_ne hside (Ne.symm (mul_ne_zero hb hy))

end Erdos957
