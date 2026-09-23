import CertifiedSourceLocality
import DirectChargeAccounting

/-! Exact partition of the assembled charge by each donor's retained center.
No weights or donors are discarded, including in the indirect partition. -/

namespace Erdos957

noncomputable def assignedDonorCenter {n : ℕ}
    (p : Fin n → Point) (bad : Finset (Fin n)) (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p bad →
      CertifiedDonorAssignment p bad u (height u)) (u : Fin n) : Fin n := by
  classical
  exact if hu : u ∈ chargeDonors p bad then (assignments u hu).context.q else u

noncomputable def centerChargeSources {n : ℕ}
    (p : Fin n → Point) (bad : Finset (Fin n)) (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p bad →
      CertifiedDonorAssignment p bad u (height u)) (q : Fin n) : Finset (Fin n) := by
  classical
  exact (chargeDonors p bad).filter (fun u => assignedDonorCenter p bad height assignments u = q)

noncomputable def centerPacketChargeTotal {n : ℕ}
    (p : Fin n → Point) (bad : Finset (Fin n)) (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p bad →
      CertifiedDonorAssignment p bad u (height u)) (q x : Fin n) : ℕ :=
  ∑ u ∈ centerChargeSources p bad height assignments q,
    localPacketCharge p bad (certifiedFamilyPackets p bad height assignments) u x

noncomputable def centerIndirectPacketChargeTotal {n : ℕ}
    (p : Fin n → Point) (bad : Finset (Fin n)) (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p bad →
      CertifiedDonorAssignment p bad u (height u)) (q x : Fin n) : ℕ := by
  classical
  exact ∑ u ∈ (centerChargeSources p bad height assignments q).filter
    (fun u => ¬ (nearestGraph p).Adj u x),
      localPacketCharge p bad (certifiedFamilyPackets p bad height assignments) u x

theorem assignedDonorCenter_eq {n : ℕ}
    (p : Fin n → Point) (bad : Finset (Fin n)) (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p bad →
      CertifiedDonorAssignment p bad u (height u))
    (u : Fin n) (hu : u ∈ chargeDonors p bad) :
    assignedDonorCenter p bad height assignments u = (assignments u hu).context.q := by
  simp only [assignedDonorCenter, dite_eq_left hu]

/-- The actual full sum is the sum of all actual center groups. -/
theorem certified_charge_sum_eq_center_groups {n : ℕ}
    (p : Fin n → Point) (bad : Finset (Fin n)) (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p bad →
      CertifiedDonorAssignment p bad u (height u)) (x : Fin n) :
    ∑ u ∈ chargeDonors p bad,
        localPacketCharge p bad (certifiedFamilyPackets p bad height assignments) u x =
      ∑ q : Fin n, centerPacketChargeTotal p bad height assignments q x := by
  classical
  simp only [centerPacketChargeTotal, centerChargeSources, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

/-- The indirect sum has the same exact center partition. -/
theorem certified_indirect_sum_eq_center_groups {n : ℕ}
    (p : Fin n → Point) (bad : Finset (Fin n)) (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p bad →
      CertifiedDonorAssignment p bad u (height u)) (x : Fin n) :
    indirectPacketChargeTotal p bad (certifiedFamilyPackets p bad height assignments) x =
      ∑ q : Fin n, centerIndirectPacketChargeTotal p bad height assignments q x := by
  classical
  simp only [indirectPacketChargeTotal, indirectChargeSources,
    centerIndirectPacketChargeTotal, centerChargeSources, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hux : (nearestGraph p).Adj u x <;> simp [hux]

/-- Availability of a shared-five center forces every certified rule with
that center to use the same selected pair's charge function. -/
theorem CertifiedDonorRule.weight_eq_selected_sharedFive {n : ℕ}
    {p : Fin n → Point} {u q : Fin n} {height : Fin n → ℝ}
    (rule : CertifiedDonorRule p u q height)
    (available : Nonempty (SharedFiveCenterChoice p q)) (x : Fin n) :
    rule.packet.weight x = (selectedSharedFiveCenter p q available).charge u x := by
  let selected := selectedSharedFiveCenter p q available
  have hdeg := selected.center_degree
  cases rule with
  | low choice => have hl := choice.central_degree; omega
  | unique choice high =>
      have hl := choice.unique selected.left selected.center_left selected.left_diameter
      have hr := choice.unique selected.right selected.center_right selected.right_diameter
      exact False.elim (selected.base.ne (hl.trans hr.symm))
  | sharedFive available' endpoint central =>
      exact (selectedSharedFiveCenter p q available').packetFor_weight u endpoint central x
  | sharedSix choice => have hs := choice.center_degree; omega
  | reflectedSharedSix choice =>
      have hs := choice.reflected.center_degree
      have heq := nearestGraph_degree_eq_of_dist_eq p (fun i => planeReflection (p i))
        (fun i j => planeReflection.dist_map (p i) (p j)) q
      omega

/-- A center group's exact total is the fixed shared-five charge restricted
to its actual donor fiber. Eligibility of the partner is not assumed. -/
theorem centerPacketChargeTotal_eq_sharedFive_sum {n : ℕ}
    (p : Fin n → Point) (bad : Finset (Fin n)) (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p bad →
      CertifiedDonorAssignment p bad u (height u)) (q x : Fin n)
    (available : Nonempty (SharedFiveCenterChoice p q)) :
    centerPacketChargeTotal p bad height assignments q x =
      ∑ u ∈ centerChargeSources p bad height assignments q,
        (selectedSharedFiveCenter p q available).charge u x := by
  classical
  apply Finset.sum_congr rfl
  intro u hu
  obtain ⟨hud, hcenter⟩ := Finset.mem_filter.mp hu
  rw [assignedDonorCenter_eq p bad height assignments u hud] at hcenter
  subst q
  simp only [localPacketCharge, dite_eq_left hud, certifiedFamilyPackets,
    CertifiedDonorAssignment.packet]
  exact (assignments u hud).rule.weight_eq_selected_sharedFive available x

end Erdos957
