import LocalChargeAssembly

/-! Metric locality of actual packet transfers. These distance bounds do not
assert a cyclic hull neighborhood or a simultaneous receiver capacity bound. -/

namespace Erdos957

/-- A positive packet transfer travels at most two minimum-distance edges. -/
theorem LocalChargePacket.positive_dist_le_two_min {n : ℕ}
    {p : Fin n → Point} {u x : Fin n} {ij : Fin n × Fin n}
    (packet : LocalChargePacket p u) (hmin : isMinPair p ij)
    (hx : 0 < packet.weight x) :
    dist (p u) (p x) ≤ 2 * pairDist p ij := by
  rcases packet.positive_reachable x hx with hux | ⟨v, huv, hvx⟩
  · rw [nearestGraph_adj_dist_eq p hmin hux]
    have hnonneg : 0 ≤ pairDist p ij := dist_nonneg
    linarith
  · calc
      dist (p u) (p x) ≤ dist (p u) (p v) + dist (p v) (p x) :=
        dist_triangle _ _ _
      _ = 2 * pairDist p ij := by
        rw [nearestGraph_adj_dist_eq p hmin huv,
          nearestGraph_adj_dist_eq p hmin hvx]
        ring

/-- Two packet sources charging the same receiver are within four minimum
distances of one another. The sources need not be distinct. -/
theorem LocalChargePacket.sources_dist_le_four_min {n : ℕ}
    {p : Fin n → Point} {u w x : Fin n} {ij : Fin n × Fin n}
    (packet : LocalChargePacket p u) (packet' : LocalChargePacket p w)
    (hmin : isMinPair p ij)
    (hux : 0 < packet.weight x) (hwx : 0 < packet'.weight x) :
    dist (p u) (p w) ≤ 4 * pairDist p ij := by
  have hu := packet.positive_dist_le_two_min hmin hux
  have hw := packet'.positive_dist_le_two_min hmin hwx
  calc
    dist (p u) (p w) ≤ dist (p u) (p x) + dist (p x) (p w) :=
      dist_triangle _ _ _
    _ ≤ 2 * pairDist p ij + 2 * pairDist p ij := by
      rw [dist_comm (p x) (p w)]
      exact add_le_add hu hw
    _ = 4 * pairDist p ij := by ring

/-- Positivity of the assembled charge automatically identifies an actual
donor and gives the packet's two-step metric bound. -/
theorem localPacketCharge_pos_dist_le_two_min {n : ℕ}
    (p : Fin n → Point) (bad : Finset (Fin n))
    (packets : ∀ u, u ∈ chargeDonors p bad → LocalChargePacket p u)
    {u x : Fin n} {ij : Fin n × Fin n} (hmin : isMinPair p ij)
    (hux : 0 < localPacketCharge p bad packets u x) :
    dist (p u) (p x) ≤ 2 * pairDist p ij := by
  classical
  by_cases hu : u ∈ chargeDonors p bad
  · exact (packets u hu).positive_dist_le_two_min hmin
      (by simpa only [localPacketCharge, dite_eq_left hu] using hux)
  · simp only [localPacketCharge, dite_eq_right hu] at hux
    omega

/-- Any two positive sources in an assembled packet family charging the
same receiver are within four minimum distances of one another. -/
theorem localPacketCharge_sources_dist_le_four_min {n : ℕ}
    (p : Fin n → Point) (bad : Finset (Fin n))
    (packets : ∀ u, u ∈ chargeDonors p bad → LocalChargePacket p u)
    {u w x : Fin n} {ij : Fin n × Fin n} (hmin : isMinPair p ij)
    (hux : 0 < localPacketCharge p bad packets u x)
    (hwx : 0 < localPacketCharge p bad packets w x) :
    dist (p u) (p w) ≤ 4 * pairDist p ij := by
  have hu := localPacketCharge_pos_dist_le_two_min p bad packets hmin hux
  have hw := localPacketCharge_pos_dist_le_two_min p bad packets hmin hwx
  calc
    dist (p u) (p w) ≤ dist (p u) (p x) + dist (p x) (p w) :=
      dist_triangle _ _ _
    _ ≤ 2 * pairDist p ij + 2 * pairDist p ij := by
      rw [dist_comm (p x) (p w)]
      exact add_le_add hu hw
    _ = 4 * pairDist p ij := by ring

end Erdos957
