import LocalChargeAssembly

/-! Finite hull neighborhoods and exact weighted-sum restriction. Geometry
must prove support of the charge in this neighborhood before using the sum. -/

namespace Erdos957

/-- The seven cyclic positions centered at i. Repeated indices in a small
cycle are automatically counted once. -/
def hullSourceNeighborhood {n h : ℕ} [NeZero h]
    (v : Fin h → Fin n) (i : Fin h) : Finset (Fin n) :=
  ([v i, v (i + 1), v (i - 1), v ((i + 1) + 1), v ((i - 1) - 1),
    v (((i + 1) + 1) + 1), v (((i - 1) - 1) - 1)] : List (Fin n)).toFinset

theorem mem_hullSourceNeighborhood_iff {n h : ℕ} [NeZero h]
    (v : Fin h → Fin n) (i : Fin h) (w : Fin n) :
    w ∈ hullSourceNeighborhood v i ↔
      w = v i ∨ w = v (i + 1) ∨ w = v (i - 1) ∨
      w = v ((i + 1) + 1) ∨ w = v ((i - 1) - 1) ∨
      w = v (((i + 1) + 1) + 1) ∨ w = v (((i - 1) - 1) - 1) := by
  simp [hullSourceNeighborhood]

theorem hullSourceNeighborhood_card_le_seven {n h : ℕ} [NeZero h]
    (v : Fin h → Fin n) (i : Fin h) :
    (hullSourceNeighborhood v i).card ≤ 7 := by
  exact (List.toFinset_card_le _).trans (by simp)

/-- A proved positive-support bound restricts the actual total to the finite
neighborhood exactly. Ineligible vertices contribute zero; no source is counted
twice and no simultaneous contribution is discarded. -/
theorem localPacketCharge_sum_eq_neighborhood {n : ℕ}
    (p : Fin n → Point) (bad : Finset (Fin n))
    (packets : ∀ u, u ∈ chargeDonors p bad → LocalChargePacket p u)
    (N : Finset (Fin n)) (x : Fin n)
    (hwhere : ∀ u, 0 < localPacketCharge p bad packets u x → u ∈ N) :
    ∑ u ∈ chargeDonors p bad, localPacketCharge p bad packets u x =
      ∑ u ∈ N, localPacketCharge p bad packets u x := by
  classical
  calc
    ∑ u ∈ chargeDonors p bad, localPacketCharge p bad packets u x =
        ∑ u ∈ chargeDonors p bad ∩ N, localPacketCharge p bad packets u x := by
      symm
      apply Finset.sum_subset Finset.inter_subset_left
      intro u hu hnot
      apply Nat.eq_zero_of_not_pos
      intro hpos
      exact hnot (Finset.mem_inter.mpr ⟨hu, hwhere u hpos⟩)
    _ = ∑ u ∈ N, localPacketCharge p bad packets u x := by
      apply Finset.sum_subset Finset.inter_subset_right
      intro u hu hnot
      have hnotdonor : u ∉ chargeDonors p bad := by
        intro hudonor
        exact hnot (Finset.mem_inter.mpr ⟨hudonor, hu⟩)
      simp only [localPacketCharge, dite_eq_right hnotdonor]

/-- The same support bound limits the number of actual positive sources. It
does not imply the sharper weighted receiver capacity needed by the theorem. -/
theorem localPacketCharge_active_card_le_neighborhood {n : ℕ}
    (p : Fin n → Point) (bad : Finset (Fin n))
    (packets : ∀ u, u ∈ chargeDonors p bad → LocalChargePacket p u)
    (N : Finset (Fin n)) (x : Fin n)
    (hwhere : ∀ u, 0 < localPacketCharge p bad packets u x → u ∈ N) :
    ((chargeDonors p bad).filter
      (fun u => 0 < localPacketCharge p bad packets u x)).card ≤ N.card := by
  apply Finset.card_le_card
  intro u hu
  exact hwhere u (Finset.mem_filter.mp hu).2

end Erdos957
