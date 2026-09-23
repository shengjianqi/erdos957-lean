import LocalChargeAssembly

/-! Assemble local charge packets from an actual receiver weight bound. -/

namespace Erdos957

/-- A direct weighted capacity bound gives a certificate, without replacing it
by a bound on the number of contributing donors. -/
noncomputable def chargeCertificate_of_weighted_localPackets {n : ℕ}
    (p : Fin n → Point) (bad : Finset (Fin n))
    (packets : ∀ u, u ∈ chargeDonors p bad → LocalChargePacket p u)
    (hcapacity : ∀ v, v ∉ diameterEndpoints p →
      ∑ u ∈ chargeDonors p bad, localPacketCharge p bad packets u v ≤
        2 * (6 - (nearestGraph p).degree v)) :
    ChargeCertificate p := by
  classical
  refine {
    bad := bad
    charge := localPacketCharge p bad packets
    source := ?_
    capacity := ?_
  }
  · intro u hu
    change u ∈ chargeDonors p bad at hu
    simpa only [localPacketCharge, dite_eq_left hu] using
      (packets u hu).sum_weight_outside
  · intro v hv
    exact hcapacity v (Finset.mem_filter.mp hv).2

/-- The checked packet and weighted receiver obligations imply the counting
inequality for this configuration. -/
theorem charging_bound_of_weighted_localPackets {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    (bad : Finset (Fin n))
    (packets : ∀ u, u ∈ chargeDonors p bad → LocalChargePacket p u)
    (hcapacity : ∀ v, v ∉ diameterEndpoints p →
      ∑ u ∈ chargeDonors p bad, localPacketCharge p bad packets u v ≤
        2 * (6 - (nearestGraph p).degree v)) :
    sMin p + 2 * diameterEndpointCount p ≤ 3 * n + bad.card :=
  (chargeCertificate_of_weighted_localPackets p bad packets hcapacity).count_bound hn hp

/-- The total received weight is the sum of the left and right role counts.
The equality holds for arbitrary packet choices, including repeated receivers. -/
theorem localPacketCharge_sum_roles {n : ℕ}
    (p : Fin n → Point) (bad : Finset (Fin n))
    (packets : ∀ u, u ∈ chargeDonors p bad → LocalChargePacket p u)
    (v : Fin n) :
    ∑ u ∈ chargeDonors p bad, localPacketCharge p bad packets u v =
      (∑ u ∈ chargeDonors p bad,
        if hu : u ∈ chargeDonors p bad then
          if v = (packets u hu).left then 1 else 0 else 0) +
      (∑ u ∈ chargeDonors p bad,
        if hu : u ∈ chargeDonors p bad then
          if v = (packets u hu).right then 1 else 0 else 0) := by
  classical
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  simp only [localPacketCharge, dite_eq_left hu, LocalChargePacket.weight]

end Erdos957
