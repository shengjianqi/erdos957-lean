import CenterChargeGroups
import SharedCenterUniqueness

/-! Shared-five groups of the actual assembled family. Endpoint eligibility
is retained explicitly; inactive partners never contribute a fictitious unit. -/

namespace Erdos957

/-- Any eligible endpoint of a supported shared-five pair has that center
as its actual retained central neighbor. -/
theorem SharedFiveCenterChoice.endpoint_actual_center_eq {n : ℕ}
    {p : Fin n → Point} {q : Fin n} (choice : SharedFiveCenterChoice p q)
    (hp : Function.Injective p) (hn : 2 ≤ n)
    {bad : Finset (Fin n)} {u : Fin n} (ctx : DonorContext p bad u)
    (hsource : u = choice.left ∨ u = choice.right) : ctx.q = q := by
  rcases hsource with rfl | rfl
  · exact (supported_nearest_triangle_center_eq p hn hp ctx choice.base
      choice.center_left.symm choice.center_right.symm (Or.inr choice.support)).symm
  · exact (supported_nearest_triangle_center_eq p hn hp ctx choice.base.symm
      choice.center_right.symm choice.center_left.symm (Or.inl choice.support)).symm

/-- A shared-five fiber consists exactly of its eligible selected endpoints. -/
theorem mem_centerChargeSources_iff_sharedFive {n : ℕ}
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 2 ≤ n)
    (bad : Finset (Fin n)) (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p bad →
      CertifiedDonorAssignment p bad u (height u))
    (q : Fin n) (choice : SharedFiveCenterChoice p q) (u : Fin n) :
    u ∈ centerChargeSources p bad height assignments q ↔
      u ∈ chargeDonors p bad ∧ (u = choice.left ∨ u = choice.right) := by
  classical
  constructor
  · intro hu
    obtain ⟨hud, hc⟩ := Finset.mem_filter.mp hu
    rw [assignedDonorCenter_eq p bad height assignments u hud] at hc
    refine ⟨hud, choice.diameter_neighbor_cases u (assignments u hud).context.endpoint ?_⟩
    simpa only [hc] using (assignments u hud).context.central_adj.symm
  · rintro ⟨hud, he⟩
    apply Finset.mem_filter.mpr
    refine ⟨hud, ?_⟩
    rw [assignedDonorCenter_eq p bad height assignments u hud]
    exact choice.endpoint_actual_center_eq hp hn (assignments u hud).context he

/-- Exact assembled weight, with one term per eligible selected endpoint. -/
theorem centerPacketChargeTotal_sharedFive_eq_eligible_pair {n : ℕ}
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 2 ≤ n)
    (bad : Finset (Fin n)) (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p bad →
      CertifiedDonorAssignment p bad u (height u)) (q x : Fin n)
    (available : Nonempty (SharedFiveCenterChoice p q)) :
    centerPacketChargeTotal p bad height assignments q x =
      (if (selectedSharedFiveCenter p q available).left ∈ chargeDonors p bad
        then (selectedSharedFiveCenter p q available).selection.first.weight x else 0) +
      (if (selectedSharedFiveCenter p q available).right ∈ chargeDonors p bad
        then (selectedSharedFiveCenter p q available).selection.second.weight x else 0) := by
  classical
  rw [centerPacketChargeTotal_eq_sharedFive_sum p bad height assignments q x available,
    (selectedSharedFiveCenter p q available).sum_charge_eq]
  simp only [mem_centerChargeSources_iff_sharedFive p hp hn bad height assignments q
    (selectedSharedFiveCenter p q available), true_or, or_true, and_true]

/-- The complete actual group at one shared-five center respects capacity.
This does not combine it with groups having other centers. -/
theorem centerPacketChargeTotal_sharedFive_le_capacity {n : ℕ}
    (p : Fin n → Point) (bad : Finset (Fin n)) (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p bad →
      CertifiedDonorAssignment p bad u (height u)) (q x : Fin n)
    (available : Nonempty (SharedFiveCenterChoice p q)) :
    centerPacketChargeTotal p bad height assignments q x ≤
      2 * (6 - (nearestGraph p).degree x) := by
  rw [centerPacketChargeTotal_eq_sharedFive_sum p bad height assignments q x available]
  exact (selectedSharedFiveCenter p q available).sum_charge_le_capacity _ x

/-- In the degree-six-bottom branch, the entire group's noncentral charge
is at most one, including both actual endpoint donors. -/
theorem centerPacketChargeTotal_sharedFive_noncentral_le_one {n : ℕ}
    (p : Fin n → Point) (bad : Finset (Fin n)) (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p bad →
      CertifiedDonorAssignment p bad u (height u)) (q x : Fin n)
    (available : Nonempty (SharedFiveCenterChoice p q))
    (hsix : (nearestGraph p).degree (selectedSharedFiveCenter p q available).selection.bottom = 6)
    (hx : x ≠ q) : centerPacketChargeTotal p bad height assignments q x ≤ 1 := by
  rw [centerPacketChargeTotal_eq_sharedFive_sum p bad height assignments q x available]
  exact (selectedSharedFiveCenter p q available).noncentral_sum_charge_le_one _ hsix x hx

/-- A low-bottom group's only noncentral receiver is that bottom. Its weight
is precisely the number of eligible endpoints, which may be zero, one or two. -/
theorem centerPacketChargeTotal_sharedFive_low_bottom_eq {n : ℕ}
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 2 ≤ n)
    (bad : Finset (Fin n)) (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p bad →
      CertifiedDonorAssignment p bad u (height u)) (q x : Fin n)
    (available : Nonempty (SharedFiveCenterChoice p q))
    (hlow : (nearestGraph p).degree (selectedSharedFiveCenter p q available).selection.bottom ≤ 5)
    (hx : x ≠ q) :
    centerPacketChargeTotal p bad height assignments q x =
      if x = (selectedSharedFiveCenter p q available).selection.bottom then
        (if (selectedSharedFiveCenter p q available).left ∈ chargeDonors p bad then 1 else 0) +
        (if (selectedSharedFiveCenter p q available).right ∈ chargeDonors p bad then 1 else 0)
      else 0 := by
  classical
  let choice := selectedSharedFiveCenter p q available
  have hright : choice.selection.first.right = choice.selection.bottom ∧
      choice.selection.second.right = choice.selection.bottom := by
    rcases choice.selection.branch with hl | hh
    · exact hl.2
    · change (nearestGraph p).degree choice.selection.bottom ≤ 5 at hlow
      omega
  rw [centerPacketChargeTotal_sharedFive_eq_eligible_pair p hp hn bad height assignments q x available]
  change (if choice.left ∈ chargeDonors p bad then choice.selection.first.weight x else 0) +
      (if choice.right ∈ chargeDonors p bad then choice.selection.second.weight x else 0) = _
  simp only [LocalChargePacket.weight, choice.selection.first_central,
    choice.selection.second_central, hright.1, hright.2, ite_eq_right hx, zero_add]
  change (if choice.left ∈ chargeDonors p bad then (if x = choice.selection.bottom then 1 else 0) else 0) +
      (if choice.right ∈ chargeDonors p bad then (if x = choice.selection.bottom then 1 else 0) else 0) =
      if x = choice.selection.bottom then _ else 0
  by_cases hb : x = choice.selection.bottom
  · simp only [hb, ite_true]
    rfl
  · simp [hb]

end Erdos957
