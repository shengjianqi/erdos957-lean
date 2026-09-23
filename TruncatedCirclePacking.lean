import ShortArcPacking
import Mathlib.Tactic.Linarith

/-! Two-direction packing after two forbidden unit disks and a strict height cutoff. -/

namespace Erdos957

open scoped ComplexConjugate

/-- Two bins of width `r` cover the half-open interval `[0,2r)`. -/
theorem card_le_two_of_separated_in_Ico
    (s : Finset ℝ) (r : ℝ) (hr : 0 < r)
    (hinterval : ∀ t ∈ s, 0 ≤ t ∧ t < 2 * r)
    (hsep : ∀ t ∈ s, ∀ u ∈ s, t ≠ u → r ≤ |t - u|) :
    s.card ≤ 2 := by
  let bin : ℝ → ℕ := fun t => Nat.floor (t / r)
  have hbin_bounds (t : ℝ) (ht : 0 ≤ t) :
      (bin t : ℝ) * r ≤ t ∧ t < ((bin t : ℝ) + 1) * r := by
    have htdiv : 0 ≤ t / r := div_nonneg ht hr.le
    constructor
    · exact (le_div_iff₀ hr).mp (Nat.floor_le htdiv)
    · exact (div_lt_iff₀ hr).mp (Nat.lt_floor_add_one (t / r))
  have hmaps : Set.MapsTo bin (s : Set ℝ) (Finset.range 2 : Set ℕ) := by
    intro t ht
    have htint := hinterval t ht
    have htdiv : 0 ≤ t / r := div_nonneg htint.1 hr.le
    have htdiv2 : t / r < 2 := (div_lt_iff₀ hr).mpr htint.2
    exact Finset.mem_range.mpr ((Nat.floor_lt htdiv).mpr htdiv2)
  have hinj : Set.InjOn bin (s : Set ℝ) := by
    intro t ht u hu htu
    by_contra hne
    have hgap := hsep t ht u hu hne
    obtain ⟨htlo, hthi⟩ := hbin_bounds t (hinterval t ht).1
    obtain ⟨hulo, huhi⟩ := hbin_bounds u (hinterval u hu).1
    have hbin_eq : (bin t : ℝ) = (bin u : ℝ) :=
      congrArg (fun k : ℕ => (k : ℝ)) htu
    rw [← hbin_eq] at hulo huhi
    rcases le_total t u with htuord | hutord
    · have habs : |t - u| = u - t := by
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr htuord)]
      rw [habs] at hgap
      nlinarith
    · have habs : |t - u| = t - u := abs_of_nonneg (sub_nonneg.mpr hutord)
      rw [habs] at hgap
      nlinarith
  simpa using (Finset.card_le_card_of_injOn bin hmaps hinj)

/-- Unit directions in the right-facing half-open 120-degree wedge admit at
most two mutually unit-separated points. -/
theorem complex_unit_card_le_two_in_right_wedge
    (s : Finset ℂ)
    (hradius : ∀ z ∈ s, ‖z‖ = 1)
    (hrange : ∀ z ∈ s, -Real.pi / 3 ≤ z.arg ∧ z.arg < Real.pi / 3)
    (hsep : ∀ z ∈ s, ∀ w ∈ s, z ≠ w → (1 : ℝ) ≤ dist z w) :
    s.card ≤ 2 := by
  classical
  have hgap (z : ℂ) (hz : z ∈ s) (w : ℂ) (hw : w ∈ s) (hzw : z ≠ w) :
      Real.pi / 3 ≤ |z.arg - w.arg| := by
    have hz1 := hradius z hz
    have hw1 := hradius w hw
    have hz0 : z ≠ 0 := by
      intro h
      simp [h] at hz1
    have hw0 : w ≠ 0 := by
      intro h
      simp [h] at hw1
    calc
      Real.pi / 3 ≤ InnerProductGeometry.angle ((0 : ℂ) - z) (0 - w) :=
        equal_radius_angle_ge_pi_div_three (0 : ℂ) z w 1
          (by norm_num) (by simpa using hz1) (by simpa using hw1)
          (hsep z hz w hw hzw)
      _ = InnerProductGeometry.angle z w := by
        simpa only [zero_sub] using InnerProductGeometry.angle_neg_neg z w
      _ ≤ |z.arg - w.arg| := complex_angle_le_arg_gap hz0 hw0
  let angles : Finset ℝ := s.image Complex.arg
  have hcard : angles.card = s.card := by
    apply Finset.card_image_iff.mpr
    intro z hz w hw heq
    by_contra hne
    have h := hgap z hz w hw hne
    rw [heq, sub_self, abs_zero] at h
    linarith [Real.pi_pos]
  let shifted : Finset ℝ := angles.image (fun θ => θ + Real.pi / 3)
  have hshiftcard : shifted.card = angles.card := by
    dsimp [shifted]
    apply Finset.card_image_of_injective
    intro θ φ h
    linarith
  have hshiftinterval : ∀ t ∈ shifted, 0 ≤ t ∧ t < 2 * (Real.pi / 3) := by
    intro t ht
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hθ
    obtain ⟨hlo, hhi⟩ := hrange z hz
    constructor <;> linarith
  have hshiftsep : ∀ t ∈ shifted, ∀ u ∈ shifted, t ≠ u →
      Real.pi / 3 ≤ |t - u| := by
    intro t ht u hu htu
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨φ, hφ, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hθ
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hφ
    have hzw : z ≠ w := by
      intro h
      exact htu (congrArg (fun t : ℂ => t.arg + Real.pi / 3) h)
    simpa only [add_sub_add_right_eq_sub] using hgap z hz w hw hzw
  rw [← hcard, ← hshiftcard]
  exact card_le_two_of_separated_in_Ico shifted (Real.pi / 3)
    (by positivity) hshiftinterval hshiftsep

/-- The two forbidden unit disks force a surviving direction into the
right-facing half-open 120-degree wedge. -/
theorem truncated_circle_direction_arg_range (z : ℂ) (h : ℝ)
    (hh : 0 < h) (hh_sq : h ^ 2 = 3 / 4)
    (hz : ‖z‖ = 1)
    (hB : (1 : ℝ) ≤ dist z (-1))
    (hT : (1 : ℝ) ≤ dist z ((-1 / 2 : ℂ) - (h : ℂ) * Complex.I))
    (hbelow : z.im < h) :
    -Real.pi / 3 ≤ z.arg ∧ z.arg < Real.pi / 3 := by
  let T : ℂ := (-1 / 2 : ℂ) - (h : ℂ) * Complex.I
  have hTre : T.re = -(1 / 2 : ℝ) := by norm_num [T]
  have hTim : T.im = -h := by simp [T]
  have hzsq : z.re ^ 2 + z.im ^ 2 = 1 := by
    have heq := Complex.normSq_eq_norm_sq z
    rw [Complex.normSq_apply, hz] at heq
    nlinarith
  have hBsq : dist z (-1) ^ 2 = (z.re + 1) ^ 2 + z.im ^ 2 := by
    rw [dist_eq_norm, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.neg_re,
      Complex.one_re, Complex.neg_im, Complex.one_im, neg_zero, sub_zero]
    ring
  have hTsq : dist z T ^ 2 = (z.re + 1 / 2) ^ 2 + (z.im + h) ^ 2 := by
    rw [dist_eq_norm, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Complex.sub_re, Complex.sub_im, hTre, hTim]
    ring
  have hBbound : -(1 / 2 : ℝ) ≤ z.re := by
    nlinarith [sq_nonneg (dist z (-1) - 1)]
  have hTbound : -1 ≤ z.re + 2 * h * z.im := by
    change (1 : ℝ) ≤ dist z T at hT
    nlinarith [sq_nonneg (dist z T - 1)]
  have hrebound : (1 / 2 : ℝ) ≤ z.re := by
    by_contra hnot
    have hrelt : z.re < 1 / 2 := lt_of_not_ge hnot
    have hy2 : h ^ 2 ≤ z.im ^ 2 := by nlinarith [sq_nonneg (z.re + 1 / 2)]
    have hyneg : z.im ≤ -h := by
      by_contra hnot'
      have hlow : -h < z.im := lt_of_not_ge hnot'
      have hprod : 0 < (h - z.im) * (h + z.im) :=
        mul_pos (by linarith) (by linarith)
      nlinarith
    have hmul : 2 * h * z.im ≤ 2 * h * (-h) :=
      mul_le_mul_of_nonneg_left hyneg (by positivity)
    nlinarith
  have hre : z.re = Real.cos z.arg := by
    simpa only [hz, one_mul] using (Complex.norm_mul_cos_arg z).symm
  have him : z.im = Real.sin z.arg := by
    simpa only [hz, one_mul] using (Complex.norm_mul_sin_arg z).symm
  have habs : |z.arg| ≤ Real.pi / 3 := by
    by_contra hnot
    have hgt : Real.pi / 3 < |z.arg| := lt_of_not_ge hnot
    have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi
      (show 0 ≤ Real.pi / 3 by positivity) (Complex.abs_arg_le_pi z) hgt
    rw [Real.cos_pi_div_three, Real.cos_abs, ← hre] at hcos
    linarith
  have hlt : z.arg < Real.pi / 3 := by
    have hle := (abs_le.mp habs).2
    by_contra hnot
    have heq : z.arg = Real.pi / 3 := by linarith
    have hsinpos : 0 < Real.sin (Real.pi / 3) :=
      Real.sin_pos_of_mem_Ioo ⟨by positivity, by linarith [Real.pi_pos]⟩
    have hsinsq : Real.sin (Real.pi / 3) ^ 2 = 3 / 4 := by
      have hs := Real.sin_sq_add_cos_sq (Real.pi / 3)
      rw [Real.cos_pi_div_three] at hs
      nlinarith
    have hhsin : h = Real.sin (Real.pi / 3) := by
      nlinarith only [hh, hh_sq, hsinpos, hsinsq]
    have himh : z.im = h := by rw [him, heq]; exact hhsin.symm
    linarith only [himh, hbelow]
  exact ⟨by simpa only [neg_div] using (abs_le.mp habs).1, hlt⟩

/-- Among unit directions that avoid the two unit disks and stay strictly
below the cutoff, at most two can be pairwise unit-separated. -/
theorem truncated_circle_card_le_two (S : Finset ℂ) (h : ℝ)
    (hh : 0 < h) (hh_sq : h ^ 2 = 3 / 4)
    (hunit : ∀ z ∈ S, ‖z‖ = 1)
    (hB : ∀ z ∈ S, (1 : ℝ) ≤ dist z (-1))
    (hT : ∀ z ∈ S, (1 : ℝ) ≤
      dist z ((-1 / 2 : ℂ) - (h : ℂ) * Complex.I))
    (hbelow : ∀ z ∈ S, z.im < h)
    (hsep : ∀ z ∈ S, ∀ w ∈ S, z ≠ w → (1 : ℝ) ≤ dist z w) :
    S.card ≤ 2 := by
  apply complex_unit_card_le_two_in_right_wedge S hunit
  · intro z hz
    exact truncated_circle_direction_arg_range z h hh hh_sq
      (hunit z hz) (hB z hz) (hT z hz) (hbelow z hz)
  · exact hsep

end Erdos957
