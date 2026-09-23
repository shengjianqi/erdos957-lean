import ShallowDegreeFiveOverload

/-! At a degree-five receiver every nonzero doubled half-charge is exactly one.
Hence the full incoming charge is literally the number of active donor
sources.  This turns the last shallow capacity problem into the source-count
statement used in the published Lemma 3. -/

namespace Erdos957

/-- A positive contribution to a degree-five receiver is exactly one doubled
half-charge unit. -/
theorem certified_family_charge_eq_one_of_pos_degree_five {n : ℕ}
    (p : Fin n → Point) (bad : Finset (Fin n))
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p bad →
      CertifiedDonorAssignment p bad u (height u))
    (x : Fin n) (hdegree : (nearestGraph p).degree x = 5) (u : Fin n)
    (hpos : 0 < localPacketCharge p bad
      (certifiedFamilyPackets p bad height assignments) u x) :
    localPacketCharge p bad
      (certifiedFamilyPackets p bad height assignments) u x = 1 := by
  have hle := certified_family_charge_le_one_of_receiver_degree_five
    p bad height assignments x hdegree u
  omega

/-- Exact degree-five accounting: the incoming doubled charge equals the
number of certified donors that contribute positively to the receiver. -/
theorem certified_family_degree_five_charge_eq_active_card {n : ℕ}
    (p : Fin n → Point) (bad : Finset (Fin n))
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p bad →
      CertifiedDonorAssignment p bad u (height u))
    (x : Fin n) (hdegree : (nearestGraph p).degree x = 5) :
    (∑ u ∈ chargeDonors p bad,
      localPacketCharge p bad
        (certifiedFamilyPackets p bad height assignments) u x) =
      ((chargeDonors p bad).filter (fun u =>
        0 < localPacketCharge p bad
          (certifiedFamilyPackets p bad height assignments) u x)).card := by
  classical
  let f := fun u : Fin n => localPacketCharge p bad
    (certifiedFamilyPackets p bad height assignments) u x
  let A := (chargeDonors p bad).filter (fun u => 0 < f u)
  calc
    (∑ u ∈ chargeDonors p bad, f u) = ∑ u ∈ A, f u := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro u hu hnot
      exact Nat.eq_zero_of_not_pos (fun hpos =>
        hnot (Finset.mem_filter.mpr ⟨hu, hpos⟩))
    _ = ∑ _u ∈ A, (1 : ℕ) := by
      apply Finset.sum_congr rfl
      intro u hu
      have hpos : 0 < f u := (Finset.mem_filter.mp hu).2
      simpa only [f] using certified_family_charge_eq_one_of_pos_degree_five
        p bad height assignments x hdegree u (by simpa only [f] using hpos)
    _ = A.card := by simp

/-- The full two-unit receiver-capacity inequality at degree five is exactly
an at-most-two-active-sources statement. -/
theorem certified_family_degree_five_capacity_iff_active_card_le_two {n : ℕ}
    (p : Fin n → Point) (bad : Finset (Fin n))
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p bad →
      CertifiedDonorAssignment p bad u (height u))
    (x : Fin n) (hdegree : (nearestGraph p).degree x = 5) :
    (∑ u ∈ chargeDonors p bad,
      localPacketCharge p bad
        (certifiedFamilyPackets p bad height assignments) u x ≤
        2 * (6 - (nearestGraph p).degree x)) ↔
      ((chargeDonors p bad).filter (fun u =>
        0 < localPacketCharge p bad
          (certifiedFamilyPackets p bad height assignments) u x)).card ≤ 2 := by
  rw [certified_family_degree_five_charge_eq_active_card
    p bad height assignments x hdegree, hdegree]

end Erdos957
