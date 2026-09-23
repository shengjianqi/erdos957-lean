import LocalCharge
import ChargingCertificates

/-! Assemble local packets once a geometric bound on receiver congestion is proved. -/

namespace Erdos957

noncomputable def chargeDonors {n : ℕ} (p : Fin n → Point)
    (bad : Finset (Fin n)) : Finset (Fin n) :=
  (diameterEndpoints p).filter (fun u => u ∉ bad ∧ (nearestGraph p).degree u = 3)

noncomputable def localPacketCharge {n : ℕ} (p : Fin n → Point)
    (bad : Finset (Fin n))
    (packets : ∀ u, u ∈ chargeDonors p bad → LocalChargePacket p u)
    (u v : Fin n) : ℕ := by
  classical
  exact if hu : u ∈ chargeDonors p bad then (packets u hu).weight v else 0

/-- Two contributing donors suffice because each individual packet uses no
more than half the receiver's doubled degree capacity. This assumption
concerns actual positive transfers, not all adjacent diameter endpoints. -/
theorem localPacketCharge_capacity {n : ℕ} (p : Fin n → Point)
    (bad : Finset (Fin n))
    (packets : ∀ u, u ∈ chargeDonors p bad → LocalChargePacket p u)
    (v : Fin n)
    (hcongestion : ((chargeDonors p bad).filter
      (fun u => 0 < localPacketCharge p bad packets u v)).card ≤ 2) :
    ∑ u ∈ chargeDonors p bad, localPacketCharge p bad packets u v ≤
      2 * (6 - (nearestGraph p).degree v) := by
  classical
  let active := (chargeDonors p bad).filter
    (fun u => 0 < localPacketCharge p bad packets u v)
  have heq : ∑ u ∈ chargeDonors p bad, localPacketCharge p bad packets u v =
      ∑ u ∈ active, localPacketCharge p bad packets u v := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro u hu hnot
    have hzero : ¬ 0 < localPacketCharge p bad packets u v := by
      intro hpos
      exact hnot (Finset.mem_filter.mpr ⟨hu, hpos⟩)
    omega
  rw [heq]
  calc
    ∑ u ∈ active, localPacketCharge p bad packets u v ≤
        ∑ _u ∈ active, (6 - (nearestGraph p).degree v) := by
      apply Finset.sum_le_sum
      intro u hu
      have hudonor := (Finset.mem_filter.mp hu).1
      simpa only [localPacketCharge, dite_eq_left hudonor] using
        (packets u hudonor).weight_le_degree_slack v
    _ = active.card * (6 - (nearestGraph p).degree v) := by simp
    _ ≤ 2 * (6 - (nearestGraph p).degree v) :=
      Nat.mul_le_mul_right _ hcongestion

/-- Local packet choices and a proved two-donor congestion bound produce the
full charge certificate. Neither hypothesis is asserted for general configurations. -/
noncomputable def chargeCertificate_of_localPackets {n : ℕ}
    (p : Fin n → Point) (bad : Finset (Fin n))
    (packets : ∀ u, u ∈ chargeDonors p bad → LocalChargePacket p u)
    (hcongestion : ∀ v, ((chargeDonors p bad).filter
      (fun u => 0 < localPacketCharge p bad packets u v)).card ≤ 2) :
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
    simpa only [localPacketCharge, dite_eq_left hu] using (packets u hu).sum_weight_outside
  · intro v _hv
    exact localPacketCharge_capacity p bad packets v (hcongestion v)

theorem charging_bound_of_localPackets {n : ℕ}
    (p : Fin n → Point) (hn : 2 ≤ n) (hp : Function.Injective p)
    (bad : Finset (Fin n))
    (packets : ∀ u, u ∈ chargeDonors p bad → LocalChargePacket p u)
    (hcongestion : ∀ v, ((chargeDonors p bad).filter
      (fun u => 0 < localPacketCharge p bad packets u v)).card ≤ 2) :
    sMin p + 2 * diameterEndpointCount p ≤ 3 * n + bad.card :=
  (chargeCertificate_of_localPackets p bad packets hcongestion).count_bound hn hp

end Erdos957
