import ShortArcPacking
import Mathlib.Tactic.Ring

/-! Forbidden angular sectors for nearest neighbors about two unit-separated centers. -/

namespace Erdos957

open scoped ComplexConjugate

theorem shifted_unit_circle_distance_sq_lt_one (γ φ : ℝ)
    (hγ : 0 < γ) (hγφ : γ < φ) (hφ : φ < Real.pi) :
    (1 + Real.cos φ - Real.cos γ) ^ 2 +
      (Real.sin φ - Real.sin γ) ^ 2 < 1 := by
  have hφpos : 0 < φ := lt_trans hγ hγφ
  have hhalf : 0 < Real.cos (φ / 2) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], by linarith⟩
  have habs : |γ - φ / 2| < φ / 2 := abs_lt.mpr ⟨by linarith, by linarith⟩
  have hcos : Real.cos (φ / 2) < Real.cos (γ - φ / 2) := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi
      (abs_nonneg (γ - φ / 2)) (show φ / 2 ≤ Real.pi by linarith) habs
    simpa only [Real.cos_abs] using h
  have hprod := mul_lt_mul_of_pos_left hcos hhalf
  have hdouble : Real.cos φ = 2 * Real.cos (φ / 2) ^ 2 - 1 := by
    rw [← Real.cos_two_mul]
    congr 1
    ring
  have hsum : Real.cos γ + Real.cos (φ - γ) =
      2 * Real.cos (φ / 2) * Real.cos (γ - φ / 2) := by
    rw [Real.cos_add_cos]
    rw [show (γ + (φ - γ)) / 2 = φ / 2 by ring,
      show (γ - (φ - γ)) / 2 = γ - φ / 2 by ring]
  have hbound : 1 + Real.cos φ < Real.cos γ + Real.cos (φ - γ) := by
    rw [hdouble, hsum]
    nlinarith
  rw [Real.cos_sub] at hbound
  nlinarith [Real.sin_sq_add_cos_sq φ, Real.sin_sq_add_cos_sq γ]

theorem unit_circle_shift_dist_lt_one (c z : ℂ)
    (hc : ‖c‖ = 1) (hz : ‖z‖ = 1)
    (hcarg : 0 < c.arg) (harg : c.arg < z.arg) (hzarg : z.arg < Real.pi) :
    dist c (1 + z) < 1 := by
  have hcre : c.re = Real.cos c.arg := by
    simpa only [hc, one_mul] using (Complex.norm_mul_cos_arg c).symm
  have hcim : c.im = Real.sin c.arg := by
    simpa only [hc, one_mul] using (Complex.norm_mul_sin_arg c).symm
  have hzre : z.re = Real.cos z.arg := by
    simpa only [hz, one_mul] using (Complex.norm_mul_cos_arg z).symm
  have hzim : z.im = Real.sin z.arg := by
    simpa only [hz, one_mul] using (Complex.norm_mul_sin_arg z).symm
  have hsq : dist c (1 + z) ^ 2 =
      (1 + Real.cos z.arg - Real.cos c.arg) ^ 2 +
        (Real.sin z.arg - Real.sin c.arg) ^ 2 := by
    rw [dist_eq_norm, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.one_re, Complex.one_im, zero_add, hcre, hcim, hzre, hzim]
    ring
  have h := shifted_unit_circle_distance_sq_lt_one c.arg z.arg hcarg harg hzarg
  rw [← hsq] at h
  nlinarith

theorem unit_arg_lt_pi_of_one_le_norm_add_one (z : ℂ)
    (hz : ‖z‖ = 1) (hadd : 1 ≤ ‖1 + z‖) : z.arg < Real.pi := by
  have hzsq : z.re ^ 2 + z.im ^ 2 = 1 := by
    have h := Complex.normSq_eq_norm_sq z
    rw [Complex.normSq_apply, hz] at h
    nlinarith
  have haddsq : ‖1 + z‖ ^ 2 = (1 + z.re) ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, zero_add]
    ring
  have hre : -(1 / 2 : ℝ) ≤ z.re := by nlinarith
  have hle := Complex.arg_le_pi z
  by_contra hnot
  have heq : z.arg = Real.pi := by linarith
  have hcos := Complex.norm_mul_cos_arg z
  rw [hz, heq, Real.cos_pi] at hcos
  linarith

/-- Four distinct unit directions cannot fit between the two outer nearest
directions at the other center while avoiding both of their unit disks. -/
theorem unit_two_circle_neighbors_card_le_three (S : Finset ℂ) (a c : ℂ)
    (ha : ‖a‖ = 1) (hc : ‖c‖ = 1)
    (haarg : -Real.pi < a.arg ∧ a.arg < 0)
    (hcarg : 0 < c.arg ∧ c.arg < Real.pi)
    (hspan : c.arg - a.arg < Real.pi)
    (hSunit : ∀ z ∈ S, ‖z‖ = 1)
    (hSorigin : ∀ z ∈ S, 1 ≤ ‖1 + z‖)
    (hSa : ∀ z ∈ S, 1 ≤ dist a (1 + z))
    (hSc : ∀ z ∈ S, 1 ≤ dist c (1 + z))
    (hsep : ∀ z ∈ S, ∀ w ∈ S, z ≠ w → 1 ≤ dist z w) : S.card ≤ 3 := by
  have hrange : ∀ z ∈ S, a.arg ≤ z.arg ∧ z.arg ≤ c.arg := by
    intro z hz
    have hzarg := unit_arg_lt_pi_of_one_le_norm_add_one z (hSunit z hz) (hSorigin z hz)
    constructor
    · by_contra hnot
      have hza : z.arg < a.arg := lt_of_not_ge hnot
      have haπ : a.arg ≠ Real.pi := by linarith [Real.pi_pos]
      have hzπ : z.arg ≠ Real.pi := ne_of_lt hzarg
      have haconj : (conj a).arg = -a.arg := by simp [Complex.arg_conj, haπ]
      have hzconj : (conj z).arg = -z.arg := by simp [Complex.arg_conj, hzπ]
      have hsmall := unit_circle_shift_dist_lt_one (conj a) (conj z)
        (by simpa using ha) (by simpa using hSunit z hz)
        (by rw [haconj]; linarith) (by rw [haconj, hzconj]; linarith)
        (by rw [hzconj]; linarith [Complex.neg_pi_lt_arg z])
      have heq : dist (conj a) (1 + conj z) = dist a (1 + z) := by
        rw [dist_eq_norm, show conj a - (1 + conj z) = conj (a - (1 + z)) by simp,
          Complex.norm_conj, ← dist_eq_norm]
      rw [heq] at hsmall
      linarith [hSa z hz]
    · by_contra hnot
      have hsmall := unit_circle_shift_dist_lt_one c z hc (hSunit z hz)
        hcarg.1 (lt_of_not_ge hnot) hzarg
      linarith [hSc z hz]
  exact complex_unit_circle_card_le_three_in_short_arg_interval S a.arg c.arg hspan
    hSunit hrange hsep

end Erdos957
