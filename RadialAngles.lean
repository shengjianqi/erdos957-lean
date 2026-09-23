import PlanarDirections
import PlanarOrientation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
Relating signed planar orientation to the arguments of complex directions.
-/

namespace Erdos957

open scoped ComplexConjugate

/-- The signed turn is the imaginary part of the complex cross product. -/
theorem turn_eq_im_conj_mul (c a b : Point) :
    turn c a b =
      (conj (pointToComplex (a - c)) * pointToComplex (b - c)).im := by
  simp only [pointToComplex, Complex.orthonormalBasisOneI_repr_symm_apply]
  simp [turn, Complex.mul_im]
  ring

/-- The complex determinant is the product of radii and the sine of the
difference of principal arguments. -/
theorem im_conj_mul_eq_norm_mul_sin_arg_sub (z w : ℂ) :
    (conj z * w).im = ‖z‖ * ‖w‖ * Real.sin (w.arg - z.arg) := by
  have hzre := Complex.norm_mul_cos_arg z
  have hzim := Complex.norm_mul_sin_arg z
  have hwre := Complex.norm_mul_cos_arg w
  have hwim := Complex.norm_mul_sin_arg w
  calc
    (conj z * w).im = z.re * w.im - z.im * w.re := by
      simp [Complex.mul_im]
      ring
    _ = (‖z‖ * Real.cos z.arg) * (‖w‖ * Real.sin w.arg) -
        (‖z‖ * Real.sin z.arg) * (‖w‖ * Real.cos w.arg) := by
      simp only [hzre, hzim, hwre, hwim]
    _ = ‖z‖ * ‖w‖ * Real.sin (w.arg - z.arg) := by
      rw [Real.sin_sub]
      ring

private theorem sin_nonpos_of_pi_le_of_le_two_pi {x : ℝ}
    (hπ : Real.pi ≤ x) (h2π : x ≤ 2 * Real.pi) : Real.sin x ≤ 0 := by
  have h : 0 ≤ Real.sin (x - Real.pi) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  rw [Real.sin_sub_pi] at h
  linarith

/-- A real argument strictly inside a short oriented sector is characterized
by two positive signed determinants. -/
private theorem arg_between_of_sines (α β γ : ℝ)
    (hα : -Real.pi < α) (hβ : β ≤ Real.pi)
    (hγlo : -Real.pi < γ) (hγhi : γ ≤ Real.pi)
    (hαβ : α < β) (_hspan : β - α < Real.pi)
    (hs₁ : 0 < Real.sin (γ - α))
    (hs₂ : 0 < Real.sin (β - γ)) : α < γ ∧ γ < β := by
  constructor
  · by_contra hn
    have hγα : γ ≤ α := le_of_not_gt hn
    by_cases h : -Real.pi ≤ γ - α
    · have hsin := Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith : γ - α ≤ 0) h
      linarith
    · have hsin := sin_nonpos_of_pi_le_of_le_two_pi
        (show Real.pi ≤ β - γ by linarith)
        (show β - γ ≤ 2 * Real.pi by linarith)
      linarith
  · by_contra hn
    have hβγ : β ≤ γ := le_of_not_gt hn
    by_cases h : -Real.pi ≤ β - γ
    · have hsin := Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith : β - γ ≤ 0) h
      linarith
    · have hsin := sin_nonpos_of_pi_le_of_le_two_pi
        (show Real.pi ≤ γ - α by linarith)
        (show γ - α ≤ 2 * Real.pi by linarith)
      linarith

/-- Positive orientation of two nonzero rays whose principal arguments differ
by an amount between zero and π. -/
theorem turn_pos_of_arg_gap (c a b : Point)
    (ha : a ≠ c) (hb : b ≠ c)
    (harg : (pointToComplex (a - c)).arg < (pointToComplex (b - c)).arg)
    (hgap : (pointToComplex (b - c)).arg - (pointToComplex (a - c)).arg < Real.pi) :
    0 < turn c a b := by
  have haz : pointToComplex (a - c) ≠ 0 := by
    intro h
    have h' : a - c = 0 := pointToComplex.injective (by simpa using h)
    exact ha (sub_eq_zero.mp h')
  have hbz : pointToComplex (b - c) ≠ 0 := by
    intro h
    have h' : b - c = 0 := pointToComplex.injective (by simpa using h)
    exact hb (sub_eq_zero.mp h')
  rw [turn_eq_im_conj_mul, im_conj_mul_eq_norm_mul_sin_arg_sub]
  exact mul_pos (mul_pos (norm_pos_iff.mpr haz) (norm_pos_iff.mpr hbz))
    (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr harg) hgap)

/-- Positive orientation across the cut from principal argument π to -π.
The inequality `π < arg(a-c) - arg(b-c)` expresses a wrapped gap under π. -/
theorem turn_pos_of_wrapped_arg_gap (c a b : Point)
    (ha : a ≠ c) (hb : b ≠ c)
    (hwrap : Real.pi < (pointToComplex (a - c)).arg -
      (pointToComplex (b - c)).arg) :
    0 < turn c a b := by
  let za := pointToComplex (a - c)
  let zb := pointToComplex (b - c)
  have haz : za ≠ 0 := by
    intro h
    exact ha (sub_eq_zero.mp (pointToComplex.injective (by simpa [za] using h)))
  have hbz : zb ≠ 0 := by
    intro h
    exact hb (sub_eq_zero.mp (pointToComplex.injective (by simpa [zb] using h)))
  change Real.pi < za.arg - zb.arg at hwrap
  have hβ := (Complex.arg_mem_Ioc zb).1
  have hα := (Complex.arg_mem_Ioc za).2
  have hsin : 0 < Real.sin (zb.arg - za.arg) := by
    have hpos : 0 < zb.arg - za.arg + 2 * Real.pi := by linarith
    have hlt : zb.arg - za.arg + 2 * Real.pi < Real.pi := by linarith
    have := Real.sin_pos_of_pos_of_lt_pi hpos hlt
    rwa [Real.sin_add_two_pi] at this
  rw [turn_eq_im_conj_mul, im_conj_mul_eq_norm_mul_sin_arg_sub]
  exact mul_pos (mul_pos (norm_pos_iff.mpr haz) (norm_pos_iff.mpr hbz)) hsin

/-- Two strictly positive turns place the third ray between the first and
last principal arguments, when these bound a sector shorter than π. -/
theorem radial_sector_arg_between (c a b q : Point)
    (ha : a ≠ c) (hb : b ≠ c) (hq : q ≠ c)
    (harg : (pointToComplex (a - c)).arg < (pointToComplex (b - c)).arg)
    (hgap : (pointToComplex (b - c)).arg - (pointToComplex (a - c)).arg < Real.pi)
    (ht₁ : 0 < turn c a q) (ht₂ : 0 < turn c q b) :
    (pointToComplex (a - c)).arg < (pointToComplex (q - c)).arg ∧
      (pointToComplex (q - c)).arg < (pointToComplex (b - c)).arg := by
  let za := pointToComplex (a - c)
  let zb := pointToComplex (b - c)
  let zq := pointToComplex (q - c)
  have hna : 0 < ‖za‖ := by
    apply norm_pos_iff.mpr
    intro hz
    exact ha (sub_eq_zero.mp (pointToComplex.injective (by simpa [za] using hz)))
  have hnb : 0 < ‖zb‖ := by
    apply norm_pos_iff.mpr
    intro hz
    exact hb (sub_eq_zero.mp (pointToComplex.injective (by simpa [zb] using hz)))
  have hnq : 0 < ‖zq‖ := by
    apply norm_pos_iff.mpr
    intro hz
    exact hq (sub_eq_zero.mp (pointToComplex.injective (by simpa [zq] using hz)))
  have hs₁ : 0 < Real.sin (zq.arg - za.arg) := by
    rw [turn_eq_im_conj_mul, im_conj_mul_eq_norm_mul_sin_arg_sub] at ht₁
    change 0 < ‖za‖ * ‖zq‖ * Real.sin (zq.arg - za.arg) at ht₁
    by_contra hn
    have := mul_nonpos_of_nonneg_of_nonpos (mul_pos hna hnq).le (le_of_not_gt hn)
    linarith
  have hs₂ : 0 < Real.sin (zb.arg - zq.arg) := by
    rw [turn_eq_im_conj_mul, im_conj_mul_eq_norm_mul_sin_arg_sub] at ht₂
    change 0 < ‖zq‖ * ‖zb‖ * Real.sin (zb.arg - zq.arg) at ht₂
    by_contra hn
    have := mul_nonpos_of_nonneg_of_nonpos (mul_pos hnq hnb).le (le_of_not_gt hn)
    linarith
  exact arg_between_of_sines za.arg zb.arg zq.arg
    (Complex.arg_mem_Ioc za).1 (Complex.arg_mem_Ioc zb).2
    (Complex.arg_mem_Ioc zq).1 (Complex.arg_mem_Ioc zq).2
    harg hgap hs₁ hs₂

end Erdos957
