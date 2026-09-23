import Foundations
import Algebra

/-!
The original sufficient geometric estimates for Erdős problem 957.

No theorem in this file assumes the published geometric estimates as axioms.
The final theorem is explicitly conditional on `GeometricEstimate`.
-/

namespace Erdos957

/-- A point is a diameter endpoint if it belongs to a maximum-distance pair. -/
noncomputable def diameterEndpoints {n : ℕ} (p : Fin n → Point) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i =>
    ∃ ij : Fin n × Fin n, isMaxPair p ij ∧ (i = ij.1 ∨ i = ij.2)

/-- Number of diameter endpoints. -/
noncomputable def diameterEndpointCount {n : ℕ} (p : Fin n → Point) : ℕ :=
  (diameterEndpoints p).card

theorem diameterEndpointCount_le {n : ℕ} (p : Fin n → Point) :
    diameterEndpointCount p ≤ n := by
  classical
  unfold diameterEndpointCount diameterEndpoints
  calc
    (Finset.univ.filter fun i : Fin n =>
        ∃ ij : Fin n × Fin n, isMaxPair p ij ∧ (i = ij.1 ∨ i = ij.2)).card
        ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
    _ = n := by simp

/-- A sufficient pair of estimates with `K` uniform over all configurations.
The diameter bound is now proved in `DiameterBound.lean`. The more economical
route in `ChargingReduction.lean` only requires the charging bound when
`n ≤ 3 * diameterEndpointCount p`, and handles the other regime separately. -/
def GeometricEstimate : Prop :=
  ∃ K : ℕ, ∀ (n : ℕ) (p : Fin n → Point),
    2 ≤ n → Function.Injective p →
      sMax p ≤ diameterEndpointCount p ∧
      sMin p + 2 * diameterEndpointCount p ≤ 3 * n + K

/-- Once the two geometric estimates are proved, the desired published
quantitative bound follows by a checked algebraic argument. This is a
conditional reduction, not a proof of `QuantitativeBound`. -/
theorem quantitative_of_geometric_estimate
    (hgeom : GeometricEstimate) : QuantitativeBound := by
  obtain ⟨K, hK⟩ := hgeom
  refine ⟨(K : ℝ), by positivity, ?_⟩
  intro n p hn hp
  obtain ⟨hMax, hMin⟩ := hK n p hn hp
  have hD := diameterEndpointCount_le p
  have hBound := ExtremeDistances.product_bound_nat
    n (sMin p) (sMax p) (diameterEndpointCount p) K hMax hD hMin
  have hBoundReal :
      (8 : ℝ) * (sMin p : ℝ) * (sMax p : ℝ) ≤
        9 * (n : ℝ) ^ 2 + 8 * (K : ℝ) * (n : ℝ) := by
    exact_mod_cast hBound
  nlinarith

/-- The original asymptotic formulation, with one threshold for every
configuration of size at least that threshold. -/
def AsymptoticBound : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ (n : ℕ) (p : Fin n → Point),
      N ≤ n → 2 ≤ n → Function.Injective p →
        (sMin p : ℝ) * (sMax p : ℝ) ≤
          ((9 / 8 : ℝ) + ε) * (n : ℝ) ^ 2

/-- A uniform linear error proves the `9/8 + o(1)` statement. -/
theorem asymptotic_of_quantitative (h : QuantitativeBound) :
    AsymptoticBound := by
  obtain ⟨C, hC, hBound⟩ := h
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (C / ε)
  refine ⟨N, ?_⟩
  intro n p hn hn2 hinj
  have hnReal : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hCn : C ≤ ε * (n : ℝ) := by
    have hCe : C ≤ (n : ℝ) * ε :=
      (div_le_iff₀ hε).mp ((le_of_lt hN).trans hnReal)
    simpa [mul_comm] using hCe
  have hCnn : C * (n : ℝ) ≤ ε * (n : ℝ) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hCn (Nat.cast_nonneg n)]
  have hProduct := hBound n p hn2 hinj
  nlinarith

end Erdos957
