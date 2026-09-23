import CertifiedSourceLocality
import DirectChargeAccounting

/-! An indirect certified transfer contains at most one doubled charge unit.
The resulting finite-sum bounds retain every positive indirect source. -/

namespace Erdos957

/-- Every retained rule sends its first unit directly to a nearest neighbor. -/
theorem CertifiedDonorRule.left_adj {n : ℕ} {p : Fin n → Point}
    {u q : Fin n} {height : Fin n → ℝ} (rule : CertifiedDonorRule p u q height) :
    (nearestGraph p).Adj u rule.packet.left := by
  classical
  cases rule with
  | low choice =>
    simpa only [CertifiedDonorRule.packet, choice.left_eq] using choice.central_adj
  | unique choice _ =>
    change (nearestGraph p).Adj u choice.packet.left
    apply choice.positive_adj
    simp [LocalChargePacket.weight]
  | sharedFive available hu hqu =>
    let choice := selectedSharedFiveCenter p q available
    change (nearestGraph p).Adj u (choice.packetFor u hu hqu).left
    by_cases hl : u = choice.left
    · subst u
      simpa [SharedFiveCenterChoice.packetFor,
        choice.selection.first_central] using hqu.symm
    · have hr := (choice.diameter_neighbor_cases u hu hqu).resolve_left hl
      subst u
      simpa [SharedFiveCenterChoice.packetFor, choice.base.ne.symm,
        choice.selection.second_central] using hqu.symm
  | sharedSix choice =>
    simpa only [CertifiedDonorRule.packet, choice.packet_left] using choice.outer_adj_source
  | reflectedSharedSix choice =>
    simpa only [CertifiedDonorRule.packet, choice.packet_sites.1] using
      choice.original_neighbors.2.2.1

/-- An indirect receiver cannot receive the first unit, and therefore
receives at most one unit from any certified donor rule. -/
theorem CertifiedDonorRule.weight_le_one_of_not_adj {n : ℕ} {p : Fin n → Point}
    {u q : Fin n} {height : Fin n → ℝ} (rule : CertifiedDonorRule p u q height)
    (x : Fin n) (hnot : ¬ (nearestGraph p).Adj u x) : rule.packet.weight x ≤ 1 := by
  have hxleft : x ≠ rule.packet.left := fun heq => hnot (heq ▸ rule.left_adj)
  simp only [LocalChargePacket.weight, ite_eq_right hxleft, zero_add]
  split_ifs <;> omega

/-- The assembled family keeps the individual indirect unit bound, including
indices outside the donor set, whose contribution is zero. -/
theorem certified_family_charge_le_one_of_not_adj {n : ℕ}
    (p : Fin n → Point) (bad : Finset (Fin n)) (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p bad →
      CertifiedDonorAssignment p bad u (height u))
    (u x : Fin n) (hnot : ¬ (nearestGraph p).Adj u x) :
    localPacketCharge p bad (certifiedFamilyPackets p bad height assignments) u x ≤ 1 := by
  classical
  by_cases hu : u ∈ chargeDonors p bad
  · simpa only [localPacketCharge, dite_eq_left hu, certifiedFamilyPackets,
      CertifiedDonorAssignment.packet] using
      (assignments u hu).rule.weight_le_one_of_not_adj x hnot
  · simp only [localPacketCharge, dite_eq_right hu, Nat.zero_le]

private theorem sum_le_positive_card_of_unit_bound {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ι → ℕ) (hunit : ∀ a ∈ S, f a ≤ 1) :
    ∑ a ∈ S, f a ≤ (S.filter (fun a => 0 < f a)).card := by
  calc
    ∑ a ∈ S, f a = ∑ a ∈ S.filter (fun a => 0 < f a), f a := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro a ha hnot
      exact Nat.eq_zero_of_not_pos (fun hpos => hnot (Finset.mem_filter.mpr ⟨ha, hpos⟩))
    _ ≤ ∑ _a ∈ S.filter (fun a => 0 < f a), (1 : ℕ) := by
      apply Finset.sum_le_sum
      intro a ha
      exact hunit a (Finset.mem_filter.mp ha).1
    _ = (S.filter (fun a => 0 < f a)).card := by simp

/-- The complete indirect sum is bounded by the number of its positive
sources. Zero contributions are removed exactly, not estimated as positive. -/
theorem certified_family_indirect_sum_le_positive_sources_card {n : ℕ}
    (p : Fin n → Point) (bad : Finset (Fin n)) (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p bad →
      CertifiedDonorAssignment p bad u (height u)) (x : Fin n) :
    let packets := certifiedFamilyPackets p bad height assignments
    indirectPacketChargeTotal p bad packets x ≤
      ((indirectChargeSources p bad x).filter (fun u =>
        0 < localPacketCharge p bad packets u x)).card := by
  apply sum_le_positive_card_of_unit_bound
  intro u hu
  exact certified_family_charge_le_one_of_not_adj p bad height assignments u x
    (Finset.mem_filter.mp hu).2

/-- When a receiver has no diameter neighbor, every certified contribution
is indirect and the full incoming sum obeys the positive-source count. -/
theorem certified_family_total_le_positive_sources_card_of_no_diameter_neighbor {n : ℕ}
    (p : Fin n → Point) (bad : Finset (Fin n)) (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p bad →
      CertifiedDonorAssignment p bad u (height u)) (x : Fin n)
    (hno : ∀ a, (nearestGraph p).Adj x a → a ∉ diameterEndpoints p) :
    let packets := certifiedFamilyPackets p bad height assignments
    (∑ u ∈ chargeDonors p bad, localPacketCharge p bad packets u x) ≤
      ((chargeDonors p bad).filter (fun u => 0 < localPacketCharge p bad packets u x)).card := by
  apply sum_le_positive_card_of_unit_bound
  intro u hu
  exact certified_family_charge_le_one_of_not_adj p bad height assignments u x
    (fun hux => hno u hux.symm (Finset.mem_filter.mp hu).1)

end Erdos957
