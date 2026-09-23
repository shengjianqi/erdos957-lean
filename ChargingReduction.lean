import DiameterBound
import NearestBound

/-! The remaining uniform charging estimate after the diameter graph bound. -/

namespace Erdos957

/-- The unproved uniform charging estimate in the regime used by the paper,
where at least a third of the points are diameter endpoints. This definition
introduces a proposition only, and does not assert that it holds. -/
def ChargingEstimate : Prop :=
  ∃ K : ℕ, ∀ (n : ℕ) (p : Fin n → Point),
    2 ≤ n → Function.Injective p →
      n ≤ 3 * diameterEndpointCount p →
      sMin p + 2 * diameterEndpointCount p ≤ 3 * n + K

/-- If at most a third of the points are diameter endpoints, the elementary
degree and diameter bounds already imply a product bound with coefficient 1. -/
theorem product_bound_of_few_diameter_endpoints {n : ℕ} (p : Fin n → Point)
    (hn : 2 ≤ n) (hp : Function.Injective p)
    (hd : 3 * diameterEndpointCount p ≤ n) :
    sMin p * sMax p ≤ n ^ 2 := by
  have hprod := Nat.mul_le_mul (sMin_le_three_mul p hn hp)
    (sMax_le_diameterEndpointCount p hp)
  have hdn := Nat.mul_le_mul_left n hd
  nlinarith

/-- Conditional on the still unproved charging estimate, obtain the
published uniform linear-error bound with leading coefficient `9/8`. -/
theorem quantitative_of_charging (hcharge : ChargingEstimate) :
    QuantitativeBound := by
  obtain ⟨K, hK⟩ := hcharge
  refine ⟨(K : ℝ), by positivity, ?_⟩
  intro n p hn hp
  by_cases hlarge : n ≤ 3 * diameterEndpointCount p
  · have hbound := ExtremeDistances.product_bound_nat
      n (sMin p) (sMax p) (diameterEndpointCount p) K
      (sMax_le_diameterEndpointCount p hp) (diameterEndpointCount_le p)
      (hK n p hn hp hlarge)
    have hreal : (8 : ℝ) * (sMin p : ℝ) * (sMax p : ℝ) ≤
        9 * (n : ℝ) ^ 2 + 8 * (K : ℝ) * (n : ℝ) := by
      exact_mod_cast hbound
    nlinarith
  · have hsmall : 3 * diameterEndpointCount p ≤ n := by omega
    have hbound := product_bound_of_few_diameter_endpoints p hn hp hsmall
    have hreal : (sMin p : ℝ) * (sMax p : ℝ) ≤ (n : ℝ) ^ 2 := by
      exact_mod_cast hbound
    have hnonneg : 0 ≤ (K : ℝ) * (n : ℝ) := by positivity
    nlinarith [sq_nonneg (n : ℝ)]

/-- Conditional on the same charging estimate, obtain the original
asymptotic statement. -/
theorem asymptotic_of_charging (hcharge : ChargingEstimate) :
    AsymptoticBound :=
  asymptotic_of_quantitative (quantitative_of_charging hcharge)

end Erdos957
