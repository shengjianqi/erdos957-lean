import Erdos957Complete

-- Explicit external-facing statements, independent of the packaged proposition names.
example (n : ℕ) (p : Fin n → EuclideanSpace ℝ (Fin 2))
    (hn : 2 ≤ n) (hp : Function.Injective p) :
    (Erdos957.sMin p : ℝ) * (Erdos957.sMax p : ℝ) ≤
      (9 / 8 : ℝ) * (n : ℝ) ^ 2 + 25200 * (n : ℝ) :=
  Erdos957.erdos957_product_bound p hn hp

example : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
    ∀ (n : ℕ) (p : Fin n → EuclideanSpace ℝ (Fin 2)),
      N ≤ n → 2 ≤ n → Function.Injective p →
        (Erdos957.sMin p : ℝ) * (Erdos957.sMax p : ℝ) ≤
          ((9 / 8 : ℝ) + ε) * (n : ℝ) ^ 2 :=
  Erdos957.erdos957_asymptotic

#check @Erdos957.erdos957_product_bound
#check Erdos957.erdos957_quantitative
#check Erdos957.erdos957_asymptotic
#print axioms Erdos957.erdos957_product_bound
#print axioms Erdos957.erdos957_quantitative
#print axioms Erdos957.erdos957_asymptotic
