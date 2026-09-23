import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
The algebraic final step of the Erdős–Pach extreme-distance product bound.

`sMin` and `sMax` stand for the numbers of closest and farthest unordered
pairs. `d` is the number of points incident to a farthest pair. The geometric
argument is expected to establish `sMax ≤ d` and
`sMin + 2 * d ≤ 3 * n + K` for a uniform error constant `K`.
-/

namespace ExtremeDistances

theorem product_bound_real
    (n sMin sMax d K : ℝ)
    (hsMin : 0 ≤ sMin)
    (hd : 0 ≤ d)
    (hK : 0 ≤ K)
    (hMax : sMax ≤ d)
    (hD : d ≤ n)
    (hMin : sMin + 2 * d ≤ 3 * n + K) :
    8 * sMin * sMax ≤ 9 * n ^ 2 + 8 * K * n := by
  have h₁ : sMin * sMax ≤ sMin * d :=
    mul_le_mul_of_nonneg_left hMax hsMin
  have h₂ : (sMin + 2 * d) * d ≤ (3 * n + K) * d :=
    mul_le_mul_of_nonneg_right hMin hd
  have h₃ : K * d ≤ K * n :=
    mul_le_mul_of_nonneg_left hD hK
  nlinarith [sq_nonneg (3 * n - 4 * d)]

theorem product_bound_nat
    (n sMin sMax d K : ℕ)
    (hMax : sMax ≤ d)
    (hD : d ≤ n)
    (hMin : sMin + 2 * d ≤ 3 * n + K) :
    8 * sMin * sMax ≤ 9 * n ^ 2 + 8 * K * n := by
  have hMax' : (sMax : ℝ) ≤ d := by exact_mod_cast hMax
  have hD' : (d : ℝ) ≤ n := by exact_mod_cast hD
  have hMin' : (sMin : ℝ) + 2 * d ≤ 3 * n + K := by exact_mod_cast hMin
  have h := product_bound_real (n : ℝ) sMin sMax d K
    (by positivity) (by positivity) (by positivity) hMax' hD' hMin'
  exact_mod_cast h

/-- A uniform linear error term gives the coefficient `9/8 + ε` for all
sufficiently large finite configurations. -/
theorem linear_error_implies_asymptotic
    (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n sMin sMax : ℕ,
      N ≤ n →
      8 * sMin * sMax ≤ 9 * n ^ 2 + 8 * K * n →
      (sMin : ℝ) * sMax ≤ ((9 : ℝ) / 8 + ε) * n ^ 2 := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((K : ℝ) / ε)
  refine ⟨N, ?_⟩
  intro n sMin sMax hn hProduct
  have hnReal : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hKdiv : (K : ℝ) / ε ≤ n := le_trans (le_of_lt hN) hnReal
  have hK : (K : ℝ) ≤ ε * n := by
    nlinarith [(div_le_iff₀ hε).mp hKdiv]
  have hnNonneg : (0 : ℝ) ≤ n := by positivity
  have hKn : (K : ℝ) * n ≤ ε * n ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hK hnNonneg]
  have hProductReal : (8 : ℝ) * sMin * sMax ≤
      9 * (n : ℝ) ^ 2 + 8 * K * n := by
    exact_mod_cast hProduct
  nlinarith

/-- The two geometric counting estimates imply the stated asymptotic
coefficient. The threshold depends only on the uniform constant and `ε`. -/
theorem product_bound_epsilon
    (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n sMin sMax d : ℕ,
      N ≤ n →
      sMax ≤ d →
      d ≤ n →
      sMin + 2 * d ≤ 3 * n + K →
      (sMin : ℝ) * sMax ≤ ((9 : ℝ) / 8 + ε) * n ^ 2 := by
  obtain ⟨N, hN⟩ := linear_error_implies_asymptotic K ε hε
  refine ⟨N, ?_⟩
  intro n sMin sMax d hn hMax hD hMin
  exact hN n sMin sMax hn (product_bound_nat n sMin sMax d K hMax hD hMin)

end ExtremeDistances
