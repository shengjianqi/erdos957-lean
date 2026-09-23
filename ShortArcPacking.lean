import HalfplanePacking
import Mathlib.Tactic.Linarith

/-! Packing separated angles in a short real interval. -/

namespace Erdos957

/-- At most three parameters separated by at least `r` fit in a closed
interval whose width is strictly less than `3r`. -/
theorem card_le_three_of_separated_in_short_interval
    (s : Finset ℝ) (lo hi r : ℝ) (hr : 0 < r)
    (hwidth : hi - lo < 3 * r)
    (hrange : ∀ θ ∈ s, lo ≤ θ ∧ θ ≤ hi)
    (hsep : ∀ θ ∈ s, ∀ φ ∈ s, θ ≠ φ → r ≤ |θ - φ|) :
    s.card ≤ 3 := by
  classical
  let shift : ℝ → ℝ := fun θ => θ - lo
  let t := s.image shift
  have ht_interval : ∀ u ∈ t, 0 ≤ u ∧ u < 3 * r := by
    intro u hu
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨hlo, hhi⟩ := hrange θ hθ
    constructor <;> dsimp [shift] <;> linarith
  have ht_sep : ∀ u ∈ t, ∀ v ∈ t, u ≠ v → r ≤ |u - v| := by
    intro u hu v hv huv
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨φ, hφ, rfl⟩ := Finset.mem_image.mp hv
    have hne : θ ≠ φ := by
      intro h
      exact huv (congrArg shift h)
    simpa only [shift, sub_sub_sub_cancel_right] using hsep θ hθ φ hφ hne
  have hcard : t.card = s.card := by
    dsimp [t]
    apply Finset.card_image_of_injective
    intro θ φ h
    dsimp [shift] at h
    linarith
  rw [← hcard]
  exact card_le_three_of_separated_in_Ico t r hr ht_interval ht_sep

/-- At most three unit complex numbers with mutual chord distance at least
one have principal arguments in any closed interval of width below `π`. -/
theorem complex_unit_circle_card_le_three_in_short_arg_interval
    (s : Finset ℂ) (lo hi : ℝ)
    (hwidth : hi - lo < Real.pi)
    (hradius : ∀ z ∈ s, ‖z‖ = 1)
    (hrange : ∀ z ∈ s, lo ≤ z.arg ∧ z.arg ≤ hi)
    (hsep : ∀ z ∈ s, ∀ w ∈ s, z ≠ w → (1 : ℝ) ≤ dist z w) :
    s.card ≤ 3 := by
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
          (by norm_num) (by simpa using hz1) (by simpa using hw1) (hsep z hz w hw hzw)
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
  have hrange' : ∀ θ ∈ angles, lo ≤ θ ∧ θ ≤ hi := by
    intro θ hθ
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hθ
    exact hrange z hz
  have hsep' : ∀ θ ∈ angles, ∀ φ ∈ angles, θ ≠ φ →
      Real.pi / 3 ≤ |θ - φ| := by
    intro θ hθ φ hφ hne
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hθ
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hφ
    have hzw : z ≠ w := by
      intro heq
      exact hne (congrArg Complex.arg heq)
    exact hgap z hz w hw hzw
  rw [← hcard]
  apply card_le_three_of_separated_in_short_interval angles lo hi (Real.pi / 3)
  · positivity
  · nlinarith [hwidth]
  · exact hrange'
  · exact hsep'

end Erdos957
