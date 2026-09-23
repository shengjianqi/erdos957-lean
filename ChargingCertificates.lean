import ChargingAccounting
import ChargingReduction

/-! An explicit interface for the geometric construction still to be proved.
No certificate is asserted to exist here. -/

namespace Erdos957

/-- Data and checked obligations of a doubled-unit charging assignment.
`bad` contains the exceptional boundary vertices. Charges are counted only
from nonexceptional degree-three diameter endpoints into other vertices. -/
structure ChargeCertificate {n : ℕ} (p : Fin n → Point) where
  bad : Finset (Fin n)
  charge : Fin n → Fin n → ℕ
  source : ∀ u ∈ (diameterEndpoints p).filter
    (fun i => i ∉ bad ∧ (nearestGraph p).degree i = 3),
    ∑ v ∈ Finset.univ.filter (fun i : Fin n => i ∉ diameterEndpoints p),
      charge u v = 2
  capacity : ∀ v ∈ Finset.univ.filter
    (fun i : Fin n => i ∉ diameterEndpoints p),
    ∑ u ∈ (diameterEndpoints p).filter
      (fun i => i ∉ bad ∧ (nearestGraph p).degree i = 3), charge u v ≤
      2 * (6 - (nearestGraph p).degree v)

/-- A valid certificate yields the required count for its configuration. -/
theorem ChargeCertificate.count_bound {n : ℕ} {p : Fin n → Point}
    (c : ChargeCertificate p) (hn : 2 ≤ n) (hp : Function.Injective p) :
    sMin p + 2 * diameterEndpointCount p ≤ 3 * n + c.bad.card :=
  nearestGraph_charge_assignment_accounting p hn hp c.bad c.charge c.source c.capacity

/-- It suffices to construct uniformly bounded certificates for all
sufficiently large configurations in the large-diameter-endpoint regime.
The finitely many small sizes are absorbed into one explicit constant. -/
theorem chargingEstimate_of_eventual_certificates (K N : ℕ)
    (hcert : ∀ (n : ℕ) (p : Fin n → Point), 2 ≤ n →
      Function.Injective p → N ≤ n → n ≤ 3 * diameterEndpointCount p →
      ∃ c : ChargeCertificate p, c.bad.card ≤ K) :
    ChargingEstimate := by
  refine ⟨K + 2 * N, ?_⟩
  intro n p hn hp hd
  by_cases hN : N ≤ n
  · obtain ⟨c, hc⟩ := hcert n p hn hp hN hd
    have hb := c.count_bound hn hp
    omega
  · have hmin := sMin_le_three_mul p hn hp
    have hdiam := diameterEndpointCount_le p
    omega

/-- The published product target follows once these geometric certificates
are supplied, with no restriction left on the point-set size. -/
theorem quantitative_of_eventual_certificates (K N : ℕ)
    (hcert : ∀ (n : ℕ) (p : Fin n → Point), 2 ≤ n →
      Function.Injective p → N ≤ n → n ≤ 3 * diameterEndpointCount p →
      ∃ c : ChargeCertificate p, c.bad.card ≤ K) :
    QuantitativeBound :=
  quantitative_of_charging (chargingEstimate_of_eventual_certificates K N hcert)

end Erdos957
