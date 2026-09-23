import GridPacking
import ChargingCertificates

/-! A packing substitute for the paper's perimeter estimate.
Only a fixed lower bound on the diameter/minimum-distance ratio is needed
to separate the remote side of the hull in the local charging argument. -/

namespace Erdos957

/-- A planar configuration with diameter at most ten times its smallest
distance has at most 1681 points. No hull or perimeter hypothesis is used. -/
theorem card_le_1681_of_diameter_le_ten_min {n : ℕ}
    (p : Fin n → Point) (hp : Function.Injective p)
    {ij kl : Fin n × Fin n} (hmin : isMinPair p ij) (hmax : isMaxPair p kl)
    (hratio : pairDist p kl ≤ 10 * pairDist p ij) : n ≤ 1681 := by
  apply grid_packing_le_1681 p (p ij.1) (pairDist p ij)
    (pairDist_pos p hp hmin.1)
  · intro i j hij
    exact isMinPair_le_dist p hmin hij
  · intro i
    exact (isMaxPair_dist_le p hmax ij.1 i).trans hratio

/-- Above a fixed size, every longest pair is more than ten times every
shortest pair. This is enough to dispense with a perimeter estimate. -/
theorem ten_mul_min_lt_max_of_large_card {n : ℕ}
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    {ij kl : Fin n × Fin n} (hmin : isMinPair p ij) (hmax : isMaxPair p kl) :
    10 * pairDist p ij < pairDist p kl := by
  by_contra h
  exact (Nat.not_le_of_gt hn)
    (card_le_1681_of_diameter_le_ten_min p hp hmin hmax (le_of_not_gt h))

/-- It suffices to construct the geometric charge assignment when the
diameter exceeds ten times the minimum distance. Small configurations are
absorbed into the uniform constant using the proved packing bound. -/
theorem chargingEstimate_of_large_scale_certificates (K : ℕ)
    (hcert : ∀ (n : ℕ) (p : Fin n → Point) (ij kl : Fin n × Fin n),
      2 ≤ n → Function.Injective p → isMinPair p ij → isMaxPair p kl →
      n ≤ 3 * diameterEndpointCount p →
      10 * pairDist p ij < pairDist p kl →
      ∃ c : ChargeCertificate p, c.bad.card ≤ K) :
    ChargingEstimate := by
  apply chargingEstimate_of_eventual_certificates K 1682
  intro n p hn hp hlarge hd
  obtain ⟨ij, hmin⟩ := exists_min_pair p hn
  obtain ⟨kl, hmax⟩ := exists_max_pair p hn
  exact hcert n p ij kl hn hp hmin hmax hd
    (ten_mul_min_lt_max_of_large_card p hp (by omega) hmin hmax)

end Erdos957
