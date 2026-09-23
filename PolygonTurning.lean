import CyclicAngleSum
import DirectionSine

/-! Exterior turning angles of a cyclic sequence of nonzero complex edges. -/

namespace Erdos957

open scoped BigOperators ComplexConjugate

/-- Adding the full revolution to the last real angle does not change its
angle class. -/
private theorem wrapLift_coe_angle {h : ℕ} [NeZero h]
    (E : Fin h → ℝ) (i : Fin h) :
    (wrapLift E i : Real.Angle) = (E (cyclicNext i) : Real.Angle) := by
  by_cases hi : i.val + 1 = h
  · simp [wrapLift, hi, Real.Angle.coe_add, Real.Angle.coe_two_pi]
  · simp [wrapLift, hi]

/-- The principal argument of the quotient of consecutive edges equals the
lifted real-angle difference when the complex cross product is positive and
the lift difference lies inside one revolution. -/
theorem arg_div_eq_wrapLift_sub_of_cross_pos {h : ℕ} [NeZero h]
    (e : Fin h → ℂ) (E : Fin h → ℝ)
    (hE : ∀ i, (E i : Real.Angle) = (e i).arg)
    (hgap0 : ∀ i, E i < wrapLift E i)
    (hgap2 : ∀ i, wrapLift E i - E i < 2 * Real.pi)
    (hcross : ∀ i, 0 < (conj (e i) * e (cyclicNext i)).im)
    (i : Fin h) :
    (e (cyclicNext i) / e i).arg = wrapLift E i - E i := by
  let δ := wrapLift E i - E i
  have hδpos : 0 < δ := sub_pos.mpr (hgap0 i)
  have hδ2 : δ < 2 * Real.pi := hgap2 i
  have hα : (E i : Real.Angle) = ((e i).arg : Real.Angle) := hE i
  have hβ : (wrapLift E i : Real.Angle) =
      ((e (cyclicNext i)).arg : Real.Angle) := by
    rw [wrapLift_coe_angle]
    exact hE (cyclicNext i)
  have hsin : 0 < Real.sin δ := by
    exact sin_sub_pos_of_im_conj_mul_pos (e i) (e (cyclicNext i))
      (E i) (wrapLift E i) hα hβ (hcross i)
  have hδπ : δ < Real.pi := by
    by_contra hn
    have hπ : Real.pi ≤ δ := le_of_not_gt hn
    have hnonneg : 0 ≤ Real.sin (δ - Real.pi) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    rw [Real.sin_sub_pi] at hnonneg
    linarith
  have he : e i ≠ 0 := by
    intro hz
    have hc := hcross i
    simp [hz] at hc
  have henext : e (cyclicNext i) ≠ 0 := by
    intro hz
    have hc := hcross i
    simp [hz] at hc
  have hangle :
      ((e (cyclicNext i) / e i).arg : Real.Angle) = (δ : Real.Angle) := by
    calc
      ((e (cyclicNext i) / e i).arg : Real.Angle) =
          ((e (cyclicNext i)).arg : Real.Angle) -
            ((e i).arg : Real.Angle) := Complex.arg_div_coe_angle henext he
      _ = (wrapLift E i : Real.Angle) - (E i : Real.Angle) := by
        rw [hβ, hα]
      _ = (δ : Real.Angle) := by rw [Real.Angle.coe_sub]
  have hδmem : δ ∈ Set.Ioc (-Real.pi) Real.pi := ⟨by linarith, hδπ.le⟩
  have hδreal : (δ : Real.Angle).toReal = δ :=
    Real.Angle.toReal_coe_eq_self_iff_mem_Ioc.mpr hδmem
  exact (Complex.arg_coe_angle_eq_iff_eq_toReal.mp hangle).trans hδreal

/-- Positive consecutive cross products make all exterior angles strictly
between zero and π; their sum is one complete revolution. -/
theorem sum_arg_div_cyclicNext {h : ℕ} [NeZero h]
    (e : Fin h → ℂ) (E : Fin h → ℝ)
    (hE : ∀ i, (E i : Real.Angle) = (e i).arg)
    (hgap0 : ∀ i, E i < wrapLift E i)
    (hgap2 : ∀ i, wrapLift E i - E i < 2 * Real.pi)
    (hcross : ∀ i, 0 < (conj (e i) * e (cyclicNext i)).im) :
    (∀ i, 0 < (e (cyclicNext i) / e i).arg ∧
      (e (cyclicNext i) / e i).arg < Real.pi) ∧
      ∑ i : Fin h, (e (cyclicNext i) / e i).arg = 2 * Real.pi := by
  have hEq (i : Fin h) :
      (e (cyclicNext i) / e i).arg = wrapLift E i - E i :=
    arg_div_eq_wrapLift_sub_of_cross_pos e E hE hgap0 hgap2 hcross i
  constructor
  · intro i
    constructor
    · rw [hEq]
      exact sub_pos.mpr (hgap0 i)
    · rw [hEq]
      have hsin : 0 < Real.sin (wrapLift E i - E i) :=
        sin_sub_pos_of_im_conj_mul_pos (e i) (e (cyclicNext i))
          (E i) (wrapLift E i) (hE i)
          (by rw [wrapLift_coe_angle]; exact hE (cyclicNext i)) (hcross i)
      by_contra hn
      have hπ : Real.pi ≤ wrapLift E i - E i := le_of_not_gt hn
      have hnonneg : 0 ≤ Real.sin ((wrapLift E i - E i) - Real.pi) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [hgap2 i])
      rw [Real.sin_sub_pi] at hnonneg
      linarith
  · simp_rw [hEq]
    exact sum_wrapLift_sub E

/-- Actual edge directions have positive exterior angles whose sum is a full
turn, provided each edge lift lies between its two radial bounds. -/
theorem polygon_turning_angles {h : ℕ} [NeZero h] (hh : 3 ≤ h)
    (θ E : Fin h → ℝ) (e : Fin h → ℂ)
    (hθ : StrictMono θ)
    (hspan : θ ⟨h - 1, by omega⟩ - θ ⟨0, by omega⟩ < 2 * Real.pi)
    (hbetween : ∀ i, wrapLift θ i < E i ∧ E i < θ i + Real.pi)
    (hE : ∀ i, (E i : Real.Angle) = ((e i).arg : Real.Angle))
    (hcross : ∀ i, 0 < (conj (e i) * e (cyclicNext i)).im) :
    (∀ i, 0 < (e (cyclicNext i) / e i).arg ∧
      (e (cyclicNext i) / e i).arg < Real.pi) ∧
      ∑ i : Fin h, (e (cyclicNext i) / e i).arg = 2 * Real.pi := by
  have hsin (i : Fin h) : 0 < Real.sin (wrapLift E i - E i) :=
    sin_sub_pos_of_im_conj_mul_pos (e i) (e (cyclicNext i))
      (E i) (wrapLift E i) (hE i)
      (by rw [wrapLift_coe_angle]; exact hE (cyclicNext i)) (hcross i)
  have hgap (i : Fin h) :
      0 < wrapLift E i - E i ∧ wrapLift E i - E i < Real.pi :=
    cyclic_angle_gaps_pos_lt_pi hh θ E hθ hspan hbetween hsin i
  exact sum_arg_div_cyclicNext e E hE
    (fun i => sub_pos.mp (hgap i).1)
    (fun i => by linarith [(hgap i).2, Real.pi_pos]) hcross

/-- The same exterior-angle statement indexed by the vertex at which the
turn occurs. The preceding edge has index `i - 1`. -/
theorem polygon_vertex_exterior_angles {h : ℕ} [NeZero h] (hh : 3 ≤ h)
    (θ E : Fin h → ℝ) (e : Fin h → ℂ)
    (hθ : StrictMono θ)
    (hspan : θ ⟨h - 1, by omega⟩ - θ ⟨0, by omega⟩ < 2 * Real.pi)
    (hbetween : ∀ i, wrapLift θ i < E i ∧ E i < θ i + Real.pi)
    (hE : ∀ i, (E i : Real.Angle) = ((e i).arg : Real.Angle))
    (hcross : ∀ i, 0 < (conj (e i) * e (cyclicNext i)).im) :
    (∀ i, 0 < (e i / e (i - 1)).arg ∧
      (e i / e (i - 1)).arg < Real.pi) ∧
      ∑ i : Fin h, (e i / e (i - 1)).arg = 2 * Real.pi := by
  obtain ⟨hpositive, hsum⟩ :=
    polygon_turning_angles hh θ E e hθ hspan hbetween hE hcross
  have hnextprev (i : Fin h) : cyclicNext (i - 1) = i := by
    simp [cyclicNext]
  constructor
  · intro i
    simpa [hnextprev i] using hpositive (i - 1)
  · let f : Fin h → ℝ := fun i => (e i / e (i - 1)).arg
    have hsumNext : (∑ i : Fin h, f (cyclicNext i)) = ∑ i : Fin h, f i := by
      simpa only [cyclicNext] using
        (Fintype.sum_equiv (Equiv.addRight (1 : Fin h))
          (fun i => f (i + 1)) f (by intro i; rfl))
    have hf (i : Fin h) : f (cyclicNext i) = (e (cyclicNext i) / e i).arg := by
      simp [f, cyclicNext]
    calc
      (∑ i : Fin h, (e i / e (i - 1)).arg) = ∑ i : Fin h, f i := rfl
      _ = ∑ i : Fin h, f (cyclicNext i) := hsumNext.symm
      _ = ∑ i : Fin h, (e (cyclicNext i) / e i).arg := by simp_rw [hf]
      _ = 2 * Real.pi := hsum

end Erdos957
