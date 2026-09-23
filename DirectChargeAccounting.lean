import LocalChargeAssembly

/-! Exact separation of incoming charge by actual source-receiver adjacency.
The direct capacity theorem does not discard the remaining indirect sum. -/

namespace Erdos957

noncomputable def directChargeSources {n : ℕ} (p : Fin n → Point)
    (bad : Finset (Fin n)) (x : Fin n) : Finset (Fin n) := by
  classical
  exact (chargeDonors p bad).filter (fun u => (nearestGraph p).Adj u x)

noncomputable def indirectChargeSources {n : ℕ} (p : Fin n → Point)
    (bad : Finset (Fin n)) (x : Fin n) : Finset (Fin n) := by
  classical
  exact (chargeDonors p bad).filter (fun u => ¬ (nearestGraph p).Adj u x)

noncomputable def directPacketChargeTotal {n : ℕ} (p : Fin n → Point)
    (bad : Finset (Fin n))
    (packets : ∀ u, u ∈ chargeDonors p bad → LocalChargePacket p u)
    (x : Fin n) : ℕ :=
  ∑ u ∈ directChargeSources p bad x, localPacketCharge p bad packets u x

noncomputable def indirectPacketChargeTotal {n : ℕ} (p : Fin n → Point)
    (bad : Finset (Fin n))
    (packets : ∀ u, u ∈ chargeDonors p bad → LocalChargePacket p u)
    (x : Fin n) : ℕ :=
  ∑ u ∈ indirectChargeSources p bad x, localPacketCharge p bad packets u x

/-- Every actual packet contribution appears in exactly one of the two sums. -/
theorem localPacketCharge_sum_eq_direct_add_indirect {n : ℕ}
    (p : Fin n → Point) (bad : Finset (Fin n))
    (packets : ∀ u, u ∈ chargeDonors p bad → LocalChargePacket p u)
    (x : Fin n) :
    ∑ u ∈ chargeDonors p bad, localPacketCharge p bad packets u x =
      directPacketChargeTotal p bad packets x + indirectPacketChargeTotal p bad packets x := by
  classical
  unfold directPacketChargeTotal indirectPacketChargeTotal
    directChargeSources indirectChargeSources
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hux : (nearestGraph p).Adj u x <;> simp [hux]

/-- The contribution from every source adjacent to x fits the capacity when
there are at most two such donors. Indirect sources remain in the other sum. -/
theorem directPacketChargeTotal_le_capacity_of_card {n : ℕ}
    (p : Fin n → Point) (bad : Finset (Fin n))
    (packets : ∀ u, u ∈ chargeDonors p bad → LocalChargePacket p u)
    (x : Fin n) (hcard : (directChargeSources p bad x).card ≤ 2) :
    directPacketChargeTotal p bad packets x ≤ 2 * (6 - (nearestGraph p).degree x) := by
  classical
  unfold directPacketChargeTotal
  calc
    ∑ u ∈ directChargeSources p bad x, localPacketCharge p bad packets u x ≤
        ∑ _u ∈ directChargeSources p bad x, (6 - (nearestGraph p).degree x) := by
      apply Finset.sum_le_sum
      intro u hu
      have hudonor := (Finset.mem_filter.mp hu).1
      simpa only [localPacketCharge, dite_eq_left hudonor] using
        (packets u hudonor).weight_le_degree_slack x
    _ = (directChargeSources p bad x).card * (6 - (nearestGraph p).degree x) := by simp
    _ ≤ 2 * (6 - (nearestGraph p).degree x) := Nat.mul_le_mul_right _ hcard

/-- With the direct contribution already bounded, the remaining obligation
is exactly the indirect sum against unused capacity, with no double counting. -/
theorem total_capacity_iff_indirect_le_remaining {n : ℕ}
    (p : Fin n → Point) (bad : Finset (Fin n))
    (packets : ∀ u, u ∈ chargeDonors p bad → LocalChargePacket p u)
    (x : Fin n)
    (hdirect : directPacketChargeTotal p bad packets x ≤
      2 * (6 - (nearestGraph p).degree x)) :
    (∑ u ∈ chargeDonors p bad, localPacketCharge p bad packets u x ≤
      2 * (6 - (nearestGraph p).degree x)) ↔
    indirectPacketChargeTotal p bad packets x ≤
      2 * (6 - (nearestGraph p).degree x) - directPacketChargeTotal p bad packets x := by
  rw [localPacketCharge_sum_eq_direct_add_indirect]
  omega

/-- If every positive transfer to x is direct, its indirect total is zero. -/
theorem indirectPacketChargeTotal_eq_zero_of_positive_adj {n : ℕ}
    (p : Fin n → Point) (bad : Finset (Fin n))
    (packets : ∀ u, u ∈ chargeDonors p bad → LocalChargePacket p u)
    (x : Fin n)
    (hpositive : ∀ u, 0 < localPacketCharge p bad packets u x →
      (nearestGraph p).Adj u x) :
    indirectPacketChargeTotal p bad packets x = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro u hu
  apply Nat.eq_zero_of_not_pos
  intro hpos
  exact (Finset.mem_filter.mp hu).2 (hpositive u hpos)

/-- No diameter neighbor at a receiver excludes every direct source. -/
theorem directPacketChargeTotal_eq_zero_of_no_diameter_neighbor {n : ℕ}
    (p : Fin n → Point) (bad : Finset (Fin n))
    (packets : ∀ u, u ∈ chargeDonors p bad → LocalChargePacket p u)
    (x : Fin n)
    (hno : ∀ u, u ∈ diameterEndpoints p → ¬ (nearestGraph p).Adj x u) :
    directPacketChargeTotal p bad packets x = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro u hu
  obtain ⟨hudonor, hux⟩ := Finset.mem_filter.mp hu
  exact False.elim (hno u (Finset.mem_filter.mp hudonor).1 hux.symm)

end Erdos957
