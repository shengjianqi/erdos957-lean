import FourEndpointExclusion

/-! All incoming certified charge can be routed through actual neighbors
of the receiver, with at most two units at each neighbor. -/

namespace Erdos957

/-- Every indirect transfer uses the packet's first site as an actual
nearest intermediate vertex. This includes the last shared-six extension. -/
theorem CertifiedDonorRule.indirect_left_adj_receiver {n : ℕ}
    {p : Fin n → Point} {u q : Fin n} {height : Fin n → ℝ}
    (rule : CertifiedDonorRule p u q height) (x : Fin n)
    (hx : 0 < rule.packet.weight x) (hnot : ¬ (nearestGraph p).Adj u x) :
    (nearestGraph p).Adj rule.packet.left x := by
  have hright := rule.indirect_receiver_eq_right x hx hnot
  rw [hright]
  cases rule with
  | low choice => exact False.elim (hnot (choice.positive_geometry hx).1)
  | unique choice high => exact False.elim (hnot (choice.positive_adj x hx))
  | sharedFive available hu hqu =>
    let choice := selectedSharedFiveCenter p q available
    change (nearestGraph p).Adj (choice.packetFor u hu hqu).left
      (choice.packetFor u hu hqu).right
    by_cases hl : u = choice.left
    · subst u
      simpa [SharedFiveCenterChoice.packetFor, choice.selection.first_central]
        using choice.selection.first_secondary.1
    · have hr := (choice.diameter_neighbor_cases u hu hqu).resolve_left hl
      subst u
      simpa [SharedFiveCenterChoice.packetFor, choice.base.ne.symm,
        choice.selection.second_central] using choice.selection.second_secondary.1
  | sharedSix choice => exact choice.sites_adjacent
  | reflectedSharedSix choice => exact choice.original_neighbors.2.2.2.2.2.1

/-- A uniform two-source bound at every intermediate vertex bounds the
full weighted charge by twice the receiver degree. Direct contributions
retain both units; indirect contributions retain their exact unit bound. -/
theorem certified_family_total_le_twice_degree_of_direct_card
    {n : ℕ} (p : Fin n → Point) (bad : Finset (Fin n))
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p bad →
      CertifiedDonorAssignment p bad u (height u))
    (hcard : ∀ y, (directChargeSources p bad y).card ≤ 2) (x : Fin n) :
    ∑ u ∈ chargeDonors p bad,
      localPacketCharge p bad (certifiedFamilyPackets p bad height assignments) u x ≤
      2 * (nearestGraph p).degree x := by
  classical
  let S := chargeDonors p bad
  let packets := certifiedFamilyPackets p bad height assignments
  let f := fun u => localPacketCharge p bad packets u x
  let route := fun u => if hu : u ∈ S then
    if (nearestGraph p).Adj u x then u else (packets u hu).left else u
  let N := (nearestGraph p).neighborFinset x
  have hroute (u : Fin n) (hu : u ∈ S) (hpos : 0 < f u) : route u ∈ N := by
    apply ((nearestGraph p).mem_neighborFinset x (route u)).mpr
    dsimp only [route]
    rw [dite_eq_left hu]
    by_cases hadj : (nearestGraph p).Adj u x
    · simpa only [ite_eq_left hadj] using hadj.symm
    · rw [ite_eq_right hadj]
      exact ((assignments u hu).rule.indirect_left_adj_receiver x
        (by simpa only [f, localPacketCharge, dite_eq_left (show u ∈ chargeDonors p bad from hu),
          packets, certifiedFamilyPackets, CertifiedDonorAssignment.packet] using hpos) hadj).symm
  have hfiber (y : Fin n) : ∑ u ∈ S.filter (fun u => route u = y), f u ≤ 2 := by
    by_cases hyD : y ∈ diameterEndpoints p
    · have hsingle (u : Fin n) (hu : u ∈ S.filter (fun u => route u = y)) : u = y := by
        obtain ⟨hu, hry⟩ := Finset.mem_filter.mp hu
        dsimp only [route] at hry
        rw [dite_eq_left hu] at hry
        by_cases hadj : (nearestGraph p).Adj u x
        · simpa only [ite_eq_left hadj] using hry
        · rw [ite_eq_right hadj] at hry
          exact False.elim ((packets u hu).left_outside (hry.symm ▸ hyD))
      calc
        _ ≤ ∑ u ∈ S.filter (fun u => route u = y), if u = y then 2 else 0 := by
          apply Finset.sum_le_sum
          intro u hu
          rw [ite_eq_left (hsingle u hu)]
          have hud := (Finset.mem_filter.mp hu).1
          simp only [f, localPacketCharge, dite_eq_left hud, LocalChargePacket.weight]
          split_ifs <;> omega
        _ ≤ 2 := by simp only [Finset.sum_ite_eq']; split_ifs <;> omega
    · have hind (u : Fin n) (hu : u ∈ S.filter (fun u => route u = y)) :
          ¬ (nearestGraph p).Adj u x ∧ (nearestGraph p).Adj u y := by
        obtain ⟨hu, hry⟩ := Finset.mem_filter.mp hu
        dsimp only [route] at hry
        rw [dite_eq_left hu] at hry
        have hnot : ¬ (nearestGraph p).Adj u x := by
          intro hadj
          have huy : u = y := by simpa only [ite_eq_left hadj] using hry
          exact hyD (huy ▸ (Finset.mem_filter.mp hu).1)
        rw [ite_eq_right hnot] at hry
        refine ⟨hnot, ?_⟩
        have ht := (assignments u hu).rule.left_adj
        change (nearestGraph p).Adj u (packets u hu).left at ht
        simpa only [hry] using ht
      have hsub : S.filter (fun u => route u = y) ⊆ directChargeSources p bad y := by
        intro u hu
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hu).1, (hind u hu).2⟩
      calc
        _ ≤ ∑ _u ∈ S.filter (fun u => route u = y), (1 : ℕ) := by
          apply Finset.sum_le_sum
          intro u hu
          exact certified_family_charge_le_one_of_not_adj p bad height assignments u x (hind u hu).1
        _ = (S.filter (fun u => route u = y)).card := by simp
        _ ≤ (directChargeSources p bad y).card := Finset.card_le_card hsub
        _ ≤ 2 := hcard y
  have hsum : ∑ u ∈ S, f u = ∑ y ∈ N, ∑ u ∈ S.filter (fun u => route u = y), f u := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u hu
    by_cases hpos : 0 < f u
    · simp [hroute u hu hpos]
    · have hz : f u = 0 := by omega
      simp [hz]
  change ∑ u ∈ S, f u ≤ _
  rw [hsum]
  calc
    _ ≤ ∑ _y ∈ N, (2 : ℕ) := Finset.sum_le_sum (fun y _ => hfiber y)
    _ = 2 * (nearestGraph p).degree x := by
      simp [N, (nearestGraph p).card_neighborFinset_eq_degree, Nat.mul_comm]

/-- Every receiver of degree at most three satisfies its full capacity,
for all actual certified assignments on the tight-flat hull. -/
theorem certified_family_receiver_capacity_of_degree_le_three
    {n h : ℕ} [NeZero h]
    (p : Fin n → Point) (hp : Function.Injective p) (hn : 1681 < n)
    (v : Fin h → Fin n) (hv : Function.Injective v) (hh : 3 ≤ h)
    (hrange : Set.range v = (hullVertexIndices p : Set (Fin n)))
    (hsupport : ∀ i k, 0 ≤ turn (p (v i)) (p (v (i + 1))) (p k))
    (hpos : ∀ k, 0 < hullExteriorAngle p v k)
    (height : Fin n → Fin n → ℝ)
    (assignments : ∀ u, u ∈ chargeDonors p (tightHullBadVertices p v) →
      CertifiedDonorAssignment p (tightHullBadVertices p v) u (height u))
    (x : Fin n) (hdegree : (nearestGraph p).degree x ≤ 3) :
    ∑ u ∈ chargeDonors p (tightHullBadVertices p v),
      localPacketCharge p (tightHullBadVertices p v)
        (certifiedFamilyPackets p (tightHullBadVertices p v) height assignments) u x ≤
      2 * (6 - (nearestGraph p).degree x) := by
  have htotal := certified_family_total_le_twice_degree_of_direct_card p
    (tightHullBadVertices p v) height assignments
    (tight_flat_direct_sources_card_le_two p hp hn v hv hh hrange hsupport hpos) x
  omega

end Erdos957

