import CircleTriangle
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Quantitative orientation bounds for a long triangle with a nearly horizontal top. -/

namespace Erdos957

open scoped ComplexConjugate

/-- A central two-part region lies strictly inside a long triangle.  The two
rectangles cover the four hexagonal extension sites used in the charging
argument, while avoiding the outer corner `(5/2,-2)`. -/
theorem long_triangle_rectangle_strict_turns
    (L J R q : ℂ) (D : ℝ)
    (hD : 9 < D)
    (hLre : L.re ≤ -1) (hRre : 3 ≤ R.re)
    (hLimlo : -1 / 10 ≤ L.im) (hLimhi : L.im ≤ 0)
    (hRimlo : -1 / 10 ≤ R.im) (hRimhi : R.im ≤ 0)
    (hJrelo : -D / 10 ≤ J.re) (hJrehi : J.re ≤ D / 10)
    (hJim : J.im = -D)
    (hqrelo : 0 ≤ q.re) (hqrehi : q.re ≤ 5 / 2)
    (hqimlo : -2 ≤ q.im) (hqimhi : q.im ≤ -1 / 2)
    (hshape : q.re ≤ 2 ∨ -1 ≤ q.im) :
    0 < complexTurn L J R ∧
      0 < complexTurn L J q ∧
      0 < complexTurn J R q ∧
      0 < complexTurn R L q := by
  have hLJ_formula : complexTurn L J q =
      (J.re - L.re) * (q.im - L.im) + (D + L.im) * (q.re - L.re) := by
    simp [complexTurn, Complex.mul_im, hJim]
  have hJR_formula : complexTurn J R q =
      (R.re - J.re) * (q.im + D) -
        (D + R.im) * (q.re - J.re) := by
    simp [complexTurn, Complex.mul_im, hJim]
    ring
  have hRL_formula : complexTurn R L q =
      (R.re - L.re) * (-q.im) +
        (q.re - L.re) * R.im + (R.re - q.re) * L.im := by
    simp [complexTurn, Complex.mul_im]
    ring
  have hDq : 0 ≤ D + q.im := by linarith
  have haY : 0 ≤ L.im - q.im := by linarith
  have hbY : 0 ≤ R.im - q.im := by linarith
  have hLgap : 0 ≤ -1 - L.re := by linarith
  have hRgap : 0 ≤ R.re - 3 := by linarith
  have hJupper : 0 ≤ D / 10 - J.re := by linarith
  have hJlower : 0 ≤ J.re + D / 10 := by linarith
  have hX : 0 ≤ q.re := hqrelo
  have hDX : 0 ≤ D / 10 := by linarith
  have hXDX : 0 ≤ q.re + D / 10 := by linarith
  have hLX : 0 ≤ q.re - L.re := by linarith
  have hRX : 0 ≤ R.re - q.re := by linarith
  have hRLim : 0 ≤ L.im + 1 / 10 := by linarith
  have hRRim : 0 ≤ R.im + 1 / 10 := by linarith
  have hRL : 0 ≤ R.re - L.re := by linarith
  have hLbound₁ : 0 ≤ (-1 - L.re) * (D + q.im) :=
    mul_nonneg hLgap hDq
  have hLbound₂ : 0 ≤ (D / 10 - J.re) * (L.im - q.im) :=
    mul_nonneg hJupper haY
  have hLbound₃ : 0 ≤ (-L.im) * (D / 10) :=
    mul_nonneg (by linarith) hDX
  have hLbound₄ : 0 ≤ (L.im + 1 / 10) * q.re :=
    mul_nonneg hRLim hX
  have hLcoef : 0 ≤ q.re + 1 + q.im / 10 := by linarith
  have hLbound₅ : 0 ≤ (D - 9) * (q.re + 1 + q.im / 10) :=
    mul_nonneg (by linarith) hLcoef
  have hLlower :
      9 * (q.re + 1 + q.im / 10) + q.im - q.re / 10 ≤
        complexTurn L J q := by
    rw [hLJ_formula]
    nlinarith only [hLbound₁, hLbound₂, hLbound₃, hLbound₄, hLbound₅]
  have hLturn : 0 < complexTurn L J q := by
    have hbase : 0 <
        9 * (q.re + 1 + q.im / 10) + q.im - q.re / 10 := by
      linarith
    exact lt_of_lt_of_le hbase hLlower
  have hRbound₁ : 0 ≤ (R.re - 3) * (D + q.im) :=
    mul_nonneg hRgap hDq
  have hRbound₂ : 0 ≤ (J.re + D / 10) * (R.im - q.im) :=
    mul_nonneg hJlower hbY
  have hRbound₃ : 0 ≤ (-R.im) * (q.re + D / 10) :=
    mul_nonneg (by linarith) hXDX
  have hRlower :
      D * (3 - q.re + q.im / 10) + 3 * q.im ≤ complexTurn J R q := by
    rw [hJR_formula]
    nlinarith only [hRbound₁, hRbound₂, hRbound₃]
  have hRturn : 0 < complexTurn J R q := by
    rcases hshape with hleft | hright
    · have hcoef : 0 ≤ 3 - q.re + q.im / 10 := by linarith
      have hbound : 0 ≤ (D - 9) * (3 - q.re + q.im / 10) :=
        mul_nonneg (by linarith) hcoef
      have hbase : 0 < D * (3 - q.re + q.im / 10) + 3 * q.im := by
        nlinarith only [hbound, hleft, hqimlo]
      exact lt_of_lt_of_le hbase hRlower
    · have hcoef : 0 ≤ 3 - q.re + q.im / 10 := by linarith
      have hbound : 0 ≤ (D - 9) * (3 - q.re + q.im / 10) :=
        mul_nonneg (by linarith) hcoef
      have hbase : 0 < D * (3 - q.re + q.im / 10) + 3 * q.im := by
        nlinarith only [hbound, hqrehi, hright]
      exact lt_of_lt_of_le hbase hRlower
  have hRLbound₁ : 0 ≤ (R.re - L.re) * (-q.im - 1 / 2) :=
    mul_nonneg hRL (by linarith)
  have hRLbound₂ : 0 ≤ (q.re - L.re) * (R.im + 1 / 10) :=
    mul_nonneg hLX hRRim
  have hRLbound₃ : 0 ≤ (R.re - q.re) * (L.im + 1 / 10) :=
    mul_nonneg hRX hRLim
  have hRLlower : (2 / 5 : ℝ) * (R.re - L.re) ≤ complexTurn R L q := by
    rw [hRL_formula]
    nlinarith only [hRLbound₁, hRLbound₂, hRLbound₃]
  have hRLturn : 0 < complexTurn R L q := by
    have hbase : 0 < (2 / 5 : ℝ) * (R.re - L.re) := by linarith
    exact lt_of_lt_of_le hbase hRLlower
  have hsum : complexTurn L J q + complexTurn J R q +
      complexTurn R L q = complexTurn L J R := by
    simp [complexTurn, Complex.mul_im]
    ring
  constructor
  · rw [← hsum]
    positivity
  exact ⟨hLturn, hRturn, hRLturn⟩

end Erdos957
